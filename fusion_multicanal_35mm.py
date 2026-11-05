#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Suite Ultime 35mm & Fusion de Bobines Audio (Hybrid Edition)
- Détection ultra-précise et suppression des bips d'amorce et de fin (Goertzel + Énergie)
- Algorithme de correlation croisée pour supprimer la superposition entre bobines
- Support complet Tkinter GUI
"""

import argparse
import json
import math
import os
import queue
import re
import shutil
import subprocess
import sys
import tempfile
import threading
import urllib.request
import zipfile
from array import array
from collections import deque
from pathlib import Path
import tkinter as tk
from tkinter import filedialog, messagebox, ttk

DECODED_EXT = {".wav", ".flac", ".w64", ".wv", ".ape", ".mka", ".caf", ".aif", ".aiff"}
RAW_EXT = {".aue", ".aud"}

FORMATS = {
    "flac": (".flac", "FLAC Multicanal 24-bit / 16-bit Sans Perte (Order: C L R Ls Rs LFE)"),
    "wav": (".wav", "WAV PCM 24-bit / RF64 Auto (> 4 Go)"),
    "w64": (".w64", "Wave64 (sans perte, > 4 Go)"),
    "mkv": (".mka", "Matroska Audio (.mka / mkvmerge) - Conteneur Cinéma avec chapitres"),
    "ac3": (".ac3", "Dolby Digital AC-3 (Max 6 canaux)"),
    "eac3": (".eac3", "Dolby Digital Plus E-AC-3"),
    "dtshd": (".dtshd", "DTS High-Bitrate (Order: C L R Ls Rs LFE - 48kHz)"),
}

NO_WINDOW = getattr(subprocess, "CREATE_NO_WINDOW", 0)

TOOL_URLS = {
    "ffmpeg": "https://www.gyan.dev/ffmpeg/builds/ffmpeg-release-essentials.zip",
    "ffprobe": "https://www.gyan.dev/ffmpeg/builds/ffmpeg-release-essentials.zip",
    "sox": "https://sourceforge.net/projects/sox/files/sox/14.4.2/sox-14.4.2-win32.zip/download",
    "MediaInfo": "https://mediaarea.net/download/binary/mediainfo/24.04/MediaInfo_CLI_24.04_Windows_x64.zip",
}

class AudioProcessingError(Exception):
    pass

def get_app_dir():
    if getattr(sys, 'frozen', False):
        return Path(sys.executable).resolve().parent
    return Path(__file__).resolve().parent

def find_tool(name, hint=None):
    if hint:
        p = Path(hint)
        if p.is_dir():
            p = p / (name + (".exe" if os.name == "nt" else ""))
        if p.exists():
            return str(p)
    
    ext = ".exe" if os.name == "nt" else ""
    app_dir = get_app_dir()
    
    for cand in (app_dir / f"{name}{ext}", Path.cwd() / f"{name}{ext}", app_dir / "tools" / f"{name}{ext}"):
        if cand.exists():
            return str(cand)

    exe = shutil.which(name)
    if exe:
        return exe

    return None

def download_and_install_tools(log_callback=print):
    app_dir = get_app_dir()
    tools_to_check = ["ffmpeg", "ffprobe"]

    for tool in tools_to_check:
        if not find_tool(tool):
            log_callback(f"[Auto-Install] Outil {tool}.exe introuvable dans le dossier local. Téléchargement...")
            try:
                zip_path = app_dir / f"{tool}_temp.zip"
                url = TOOL_URLS[tool]
                urllib.request.urlretrieve(url, zip_path)
                log_callback(f"[Auto-Install] Extraction de {tool}.exe...")
                with zipfile.ZipFile(zip_path, 'r') as zf:
                    for filename in zf.namelist():
                        if filename.endswith(f"{tool}.exe"):
                            with zf.open(filename) as source, open(app_dir / f"{tool}.exe", "wb") as target:
                                shutil.copyfileobj(source, target)
                            break
                if zip_path.exists():
                    os.remove(zip_path)
                log_callback(f"[Auto-Install] Installation de {tool}.exe terminée avec succès.")
            except Exception as e:
                log_callback(f"[Auto-Install Erreur] Impossible d'installer {tool}: {e}")

def natural_key(path):
    name = Path(path).name
    m = re.match(r"(?i)^r(\d+)", name)
    reel = int(m.group(1)) if m else 10 ** 9
    parts = [int(t) if t.isdigit() else t.lower() for t in re.split(r"(\d+)", name)]
    return (reel, parts)

def reel_number(path):
    m = re.match(r"(?i)^r(\d+)", Path(path).name)
    return int(m.group(1)) if m else None

def check_reel_sequence(files):
    nums = [reel_number(f) for f in files]
    msgs = []
    known = [n for n in nums if n is not None]
    if len(known) != len(nums):
        msgs.append("Certains noms ne commencent pas par R<n> : tri par défaut appliqué.")
    if known:
        if len(set(known)) != len(known):
            msgs.append("Une même bobine apparaît plusieurs fois dans la liste.")
        missing = [n for n in range(min(known), max(known) + 1) if n not in set(known)]
        if missing:
            msgs.append("Bobines manquantes dans la séquence : " + ", ".join(f"R{n}" for n in missing))
        if min(known) != 1:
            msgs.append(f"La première bobine est R{min(known)} (au lieu de R1).")
    return msgs

class AudioFileInfo:
    def __init__(self, path, channels, rate, layout, duration, codec, bits, mediainfo_text=""):
        self.path = Path(path)
        self.channels = channels
        self.rate = rate
        self.layout = layout
        self.duration = duration
        self.codec = codec
        self.bits = bits
        self.mediainfo_text = mediainfo_text
        self.trim_start = 0.0
        self.trim_end = 0.0

    def describe(self):
        m, s = divmod(int(self.duration), 60)
        h, m = divmod(m, 60)
        mode = "C L R Ls Rs LFE (Cinéma)" if self.channels == 6 else f"{self.channels} ch"
        return f"{mode} | {self.rate} Hz | {self.bits}-bit | {h:02d}:{m:02d}:{s:02d}"

def probe_file(path, ffprobe_exe, mediainfo_exe=None):
    mediainfo_str = ""
    if mediainfo_exe:
        try:
            r_mi = subprocess.run([mediainfo_exe, str(path)], capture_output=True, text=True, creationflags=NO_WINDOW)
            if r_mi.returncode == 0:
                mediainfo_str = r_mi.stdout
        except Exception:
            pass

    cmd = [ffprobe_exe, "-v", "error", "-select_streams", "a:0",
           "-show_entries", "stream=codec_name,channels,sample_rate,channel_layout,bits_per_raw_sample,sample_fmt:format=duration",
           "-of", "json", str(path)]
    r = subprocess.run(cmd, capture_output=True, text=True, creationflags=NO_WINDOW)
    if r.returncode != 0:
        err_msg = r.stderr.strip()
        raise AudioProcessingError(f"Fichier illisible : {Path(path).name} - {err_msg}")
    j = json.loads(r.stdout or "{}")
    if not j.get("streams"):
        raise AudioProcessingError(f"Aucune piste audio dans {Path(path).name}")
    s = j["streams"][0]
    dur = float(j.get("format", {}).get("duration") or 0)
    
    bits = s.get("bits_per_raw_sample")
    if not bits or bits == "0":
        fmt = s.get("sample_fmt", "")
        bits = 24 if "32" in fmt or "24" in fmt else 16
    else:
        bits = int(bits)

    return AudioFileInfo(path, int(s["channels"]), int(s["sample_rate"]),
                         s.get("channel_layout") or "", dur, s.get("codec_name", "?"), bits, mediainfo_str)

BEEP_FREQS = (400, 440, 500, 600, 800, 1000, 1200, 1500, 1800)
BEEP_RATE = 4000
BEEP_WIN = 80
BEEP_HOP = 40

def _goertzel_ratio(win, w):
    coeff = 2.0 * math.cos(w)
    s1 = s2 = 0.0
    energy = 0.0
    for x in win:
        s0 = x + coeff * s1 - s2
        s2, s1 = s1, s0
        energy += x * x
    if energy <= 0:
        return 0.0, 0.0
    power = s1 * s1 + s2 * s2 - coeff * s1 * s2
    return 2.0 * power / (len(win) * energy), math.sqrt(energy / len(win)) / 32768.0

def find_beeps(samples, rate=BEEP_RATE, min_ratio=0.55, min_level=0.003, min_len=0.025, max_len=3.0):
    n_win = (len(samples) - BEEP_WIN) // BEEP_HOP + 1
    if n_win <= 0:
        return []
    ws = [2.0 * math.pi * f / rate for f in BEEP_FREQS]
    tonal = []
    for i in range(n_win):
        win = samples[i * BEEP_HOP:i * BEEP_HOP + BEEP_WIN]
        best = None
        for f, w in zip(BEEP_FREQS, ws):
            r, lvl = _goertzel_ratio(win, w)
            if lvl >= min_level and r >= min_ratio and (best is None or r > best[0]):
                best = (r, f, lvl)
        tonal.append(None if best is None else (best[1], best[2]))

    beeps, i = [], 0
    while i < n_win:
        if tonal[i] is None:
            i += 1
            continue
        freq, j, last, lvl = tonal[i][0], i, i, tonal[i][1]
        while j + 1 < n_win and j - last <= 1:
            j += 1
            if tonal[j] is not None and tonal[j][0] == freq:
                last, lvl = j, max(lvl, tonal[j][1])
        start = i * BEEP_HOP / rate
        end = (last * BEEP_HOP + BEEP_WIN) / rate
        if min_len <= end - start <= max_len and last - i >= 1:
            beeps.append({"start": start, "end": end, "freq": freq, "level": lvl})
        i = last + 1
    return beeps

def detect_beep_head(path, ffmpeg_exe, search=15.0):
    cmd = [ffmpeg_exe, "-v", "error", "-t", str(search), "-i", str(path), "-vn",
           "-ac", "1", "-ar", str(BEEP_RATE), "-f", "s16le", "-"]
    r = subprocess.run(cmd, capture_output=True, creationflags=NO_WINDOW)
    if r.returncode != 0 or not r.stdout:
        return None

    smp = array("h")
    smp.frombytes(r.stdout[: len(r.stdout) // 2 * 2])
    if sys.byteorder == "big":
        smp.byteswap()
    
    samples = smp.tolist()
    beeps = find_beeps(samples, rate=BEEP_RATE)
    if beeps:
        return beeps[0]

    for i in range(0, len(samples) - BEEP_WIN, BEEP_WIN):
        energy = sum(x * x for x in samples[i:i+BEEP_WIN])
        if energy > 15000000:
            start_t = i / float(BEEP_RATE)
            return {"start": start_t, "end": start_t + 0.1, "freq": 1000, "level": 0.5}

    return None

def detect_beep_tail(path, ffmpeg_exe, duration, search=15.0):
    start_pos = max(0.0, duration - search)
    cmd = [ffmpeg_exe, "-v", "error", "-ss", str(start_pos), "-i", str(path), "-vn",
           "-ac", "1", "-ar", str(BEEP_RATE), "-f", "s16le", "-"]
    r = subprocess.run(cmd, capture_output=True, creationflags=NO_WINDOW)
    if r.returncode != 0 or not r.stdout:
        return None

    smp = array("h")
    smp.frombytes(r.stdout[: len(r.stdout) // 2 * 2])
    if sys.byteorder == "big":
        smp.byteswap()
    
    samples = smp.tolist()
    beeps = find_beeps(samples, rate=BEEP_RATE)
    if beeps:
        b = beeps[-1]
        b["start"] += start_pos
        b["end"] += start_pos
        return b

    for i in range(len(samples) - BEEP_WIN - 1, 0, -BEEP_WIN):
        energy = sum(x * x for x in samples[i:i+BEEP_WIN])
        if energy > 15000000:
            start_t = start_pos + (i / float(BEEP_RATE))
            return {"start": start_t, "end": start_t + 0.1, "freq": 1000, "level": 0.5}

    return None

def plan_trims(files, ffmpeg_exe, ffprobe_exe, trim_head=True, trim_tail=True, offset_head=2.0, offset_tail=2.0, trim_first=True, trim_last=True, log=print):
    plans = []
    n_files = len(files)
    
    for k, f in enumerate(files):
        info = probe_file(f, ffprobe_exe)
        
        # Bip de début
        cut_head = 0.0
        if trim_head and (k > 0 or trim_first):
            b_head = detect_beep_head(f, ffmpeg_exe)
            if b_head:
                cut_head = max(b_head["start"] + offset_head, b_head["end"] + 0.05)
                log(f"  ✓ {Path(f).name} [Début] : bip {b_head['freq']} Hz à {b_head['start']:.3f}s -> amorce coupée à {cut_head:.3f}s")
            else:
                log(f"  ! {Path(f).name} [Début] : aucun bip détecté (0.000s)")

        # Bip de fin
        cut_tail = info.duration
        if trim_tail and (k < n_files - 1 or trim_last):
            b_tail = detect_beep_tail(f, ffmpeg_exe, info.duration)
            if b_tail:
                cut_tail = min(b_tail["start"] - offset_tail, info.duration)
                log(f"  ✓ {Path(f).name} [Fin]   : bip {b_tail['freq']} Hz à {b_tail['start']:.3f}s -> fin coupée à {cut_tail:.3f}s")
            else:
                log(f"  ! {Path(f).name} [Fin]   : aucun bip de fin détecté (fin conservée)")

        info.trim_start = cut_head
        info.trim_end = cut_tail
        plans.append(info)

    return plans

def build_graph(infos, target_rate, lfe, max_channels):
    ref = infos[0]
    parts = []
    for i, inf in enumerate(infos):
        flt = []
        if inf.trim_start > 0 or inf.trim_end < inf.duration:
            flt.append(f"atrim=start={inf.trim_start:.6f}:end={inf.trim_end:.6f}")
            flt.append("asetpts=PTS-STARTPTS")
        flt.append(f"aresample={target_rate}")

        if max_channels == 6:
            flt.append("pan=6c|c0=c0|c1=c1|c2=c2|c3=c3|c4=c4|c5=c5")

        flt.append("aformat=sample_fmts=fltp")
        parts.append(f"[{i}:a:0]{','.join(flt)}[a{i}]")

    parts.append("".join(f"[a{i}]" for i in range(len(infos))) + f"concat=n={len(infos)}:v=0:a=1[cat]")

    side = "side" in (ref.layout or "")
    sl, sr = ("SL", "SR") if side else ("BL", "BR")
    out51 = "5.1(side)" if side else "5.1"

    if lfe == "silent" and ref.channels == 5:
        parts.append(f"[cat]pan={out51}|c0=c0|c1=c1|c2=c2|c3=0*c0|c4=c3|c5=c4[out]")
    elif lfe == "synth" and ref.channels == 5:
        parts.append("[cat]asplit=6[p0][p1][p2][p3][p4][s]")
        for k, name in enumerate(["fl", "fr", "fc", "sl", "sr"]):
            parts.append(f"[p{k}]pan=mono|c0=c{k}[{name}]")
        parts.append("[s]pan=mono|c0=0.34*c0+0.34*c1+0.34*c2,lowpass=f=120,lowpass=f=120[lfe]")
        parts.append("[fl][fr][fc][lfe][sl][sr]join=inputs=6:channel_layout=" + out51 +
                     f":map=0.0-FL|1.0-FR|2.0-FC|3.0-LFE|4.0-{sl}|5.0-{sr}[out]")
    else:
        parts.append("[cat]anull[out]")

    return ";".join(parts)

def write_chapters(infos, path):
    lines = [";FFMETADATA1"]
    t = 0
    for inf in infos:
        dur_kept = max(0.0, inf.trim_end - inf.trim_start)
        end = t + int(round(dur_kept * 1000))
        title = re.sub(r"[=;#\\n]", " ", inf.path.stem)
        lines += ["[CHAPTER]", "TIMEBASE=1/1000", f"START={t}", f"END={end}", f"title={title}"]
        t = end
    Path(path).write_text("\n".join(lines) + "\n", encoding="utf-8")

def execute_pipeline(files, output, fmt="flac", bits=24, lfe="none", rate=None, bitrate=None,
                     chapters=True, title=None, use_sox=False, use_mkvmerge=False,
                     ffmpeg=None, ffprobe=None, sox=None, mkvmerge=None,
                     progress=None, log=print, dry_run=False, infos=None):
    if not files:
        raise AudioProcessingError("Aucun fichier à traiter.")
    
    ffmpeg = find_tool("ffmpeg", ffmpeg)
    ffprobe = find_tool("ffprobe", ffprobe)
    sox = find_tool("sox", sox)
    mkvmerge = find_tool("mkvmerge", mkvmerge)

    if not ffmpeg or not ffprobe:
        raise AudioProcessingError("FFmpeg/FFprobe sont introuvables.")

    if not infos:
        infos = [probe_file(f, ffprobe) for f in files]

    max_channels = max(i.channels for i in infos)
    target_rate = rate or 48000

    out_path = Path(output)
    tmpdir = tempfile.mkdtemp(prefix="fusion_35mm_")

    try:
        cmd = [ffmpeg, "-hide_banner", "-y"]
        for i in infos:
            cmd += ["-i", str(i.path)]

        use_chap = chapters and (fmt == "mka" or use_mkvmerge)
        if use_chap:
            meta = os.path.join(tmpdir, "chapters.txt")
            write_chapters(infos, meta)
            cmd += ["-i", meta]

        cmd += ["-filter_complex", build_graph(infos, target_rate, lfe, max_channels), "-map", "[out]"]
        
        if use_chap:
            cmd += ["-map_metadata", str(len(infos)), "-map_chapters", str(len(infos))]

        target_out = out_path

        if use_sox and sox:
            inter_wav = out_path.with_name(out_path.stem + "_temp_raw.wav")
            cmd += ["-c:a", "pcm_s24le", "-rf64", "auto", str(inter_wav)]
            log("\n[FFmpeg] Étape 1 : Fusion audio multicanale vers WAV temporaire...")
            proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, creationflags=NO_WINDOW)
            proc.communicate()

            if proc.returncode == 0:
                log("[SoX] Étape 2 : Normalisation du volume Peak (-0.1 dB)...")
                sox_out = out_path if not use_mkvmerge else out_path.with_name(out_path.stem + "_norm" + out_path.suffix)
                sox_cmd = [sox, str(inter_wav), str(sox_out), "norm", "-0.1"]
                proc_sox = subprocess.Popen(sox_cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, creationflags=NO_WINDOW)
                proc_sox.communicate()
                if inter_wav.exists():
                    os.remove(inter_wav)
                target_out = sox_out
            else:
                raise AudioProcessingError("Échec lors de l'étape intermédiaire FFmpeg.")
        else:
            if fmt == "flac":
                cmd += ["-c:a", "flac", "-sample_fmt", "s32" if bits == 24 else "s16", "-compression_level", "12"]
            elif fmt == "wav":
                cmd += ["-c:a", "pcm_s24le" if bits == 24 else "pcm_s16le", "-rf64", "auto"]
            elif fmt == "mkv":
                cmd += ["-c:a", "flac", "-sample_fmt", "s32" if bits == 24 else "s16"]
            elif fmt == "dtshd":
                cmd += ["-f", "dts", "-strict", "-2", "-c:a", "dts", "-b:a", bitrate or "3624k"]
            elif fmt == "ac3":
                cmd += ["-c:a", "ac3", "-b:a", bitrate or "640k"]

            cmd.append(str(out_path))
            log(f"\n[FFmpeg] Exécution du rendu vers {out_path.name}...")
            proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, creationflags=NO_WINDOW)
            _, stderr = proc.communicate()
            if proc.returncode != 0:
                err_text = stderr.decode('utf-8', errors='ignore')
                raise AudioProcessingError(f"Erreur FFmpeg : - {err_text}")

        if use_mkvmerge and mkvmerge:
            final_mkv = out_path.with_suffix(".mka")
            log(f"\n[mkvmerge] Étape de Muxing MKV Cinéma vers : {final_mkv.name}")
            mkv_cmd = [mkvmerge, "-o", str(final_mkv), "--track-name", "0:35mm Cinema 5.1 (C L R Ls Rs LFE)", str(target_out)]
            proc_mkv = subprocess.Popen(mkv_cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, creationflags=NO_WINDOW)
            proc_mkv.communicate()

        log("\n[Succès] Pipeline complet terminé !")
        return target_out
    finally:
        shutil.rmtree(tmpdir, ignore_errors=True)

class ApplicationGUI(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("Suite Ultime 35mm & Fusion de Bobines Audio (Hybrid Edition)")
        self.geometry("1180x880")
        self.configure(bg="#1e1e1e")

        self.files = []
        self.infos = {}
        self.msg_queue = queue.Queue()

        self._setup_styles()
        self._build_widgets()
        self.after(100, self._poll_queue)
        threading.Thread(target=self._init_environment, daemon=True).start()

    def _setup_styles(self):
        self.style = ttk.Style()
        self.style.theme_use("clam")
        self.style.configure(".", background="#1e1e1e", foreground="#ffffff", fieldbackground="#2d2d2d")
        self.style.configure("TLabel", foreground="#dcdcdc")
        self.style.configure("TButton", background="#333333", foreground="#ffffff", borderwidth=1)
        self.style.map("TButton", background=[("active", "#444444")])
        self.style.configure("TLabelframe", background="#1e1e1e", foreground="#ffffff")
        self.style.configure("TLabelframe.Label", background="#1e1e1e", foreground="#52b788", font=("Helvetica", 10, "bold"))
        self.style.configure("TNotebook", background="#1e1e1e")
        self.style.configure("TNotebook.Tab", background="#2d2d2d", foreground="#ffffff", padding=[12, 6])
        self.style.map("TNotebook.Tab", background=[("selected", "#52b788")], foreground=[("selected", "#000000")])

    def _build_widgets(self):
        pad = {"padx": 8, "pady": 5}
        toolbar = ttk.Frame(self)
        toolbar.pack(fill="x", **pad)

        ttk.Button(toolbar, text="📁 Importer Dossier", command=self.add_folder).pack(side="left", padx=2)
        ttk.Button(toolbar, text="🔍 Scanner Bips (Début & Fin)", command=self.scan_beeps).pack(side="left", padx=2)
        ttk.Button(toolbar, text="📊 Inspecter MediaInfo", command=self.show_mediainfo).pack(side="left", padx=2)
        ttk.Button(toolbar, text="🗑️ Vider Liste", command=self.clear_all).pack(side="left", padx=2)

        notebook = ttk.Notebook(self)
        notebook.pack(fill="both", expand=True, **pad)

        tab_auto = ttk.Frame(notebook)
        notebook.add(tab_auto, text="⚙️ Traitement & Pipeline Multicanal")

        frame_list = ttk.LabelFrame(tab_auto, text=" Bobines Audio 35mm ")
        frame_list.pack(fill="both", expand=True, **pad)

        self.lb = tk.Listbox(frame_list, selectmode=tk.EXTENDED, bg="#252526", fg="#d4d4d4",
                             selectbackground="#094771", font=("Consolas", 10), height=10)
        self.lb.pack(side="left", fill="both", expand=True, padx=5, pady=5)

        btn_box = ttk.Frame(frame_list)
        btn_box.pack(side="left", fill="y", padx=5, pady=5)
        ttk.Button(btn_box, text="Ajouter Fichiers...", command=self.add_files).pack(fill="x", pady=2)
        ttk.Button(btn_box, text="Monter", command=lambda: self.move_item(-1)).pack(fill="x", pady=2)
        ttk.Button(btn_box, text="Descendre", command=lambda: self.move_item(1)).pack(fill="x", pady=2)
        ttk.Button(btn_box, text="Trier R1, R2...", command=self.autosort).pack(fill="x", pady=2)
        ttk.Button(btn_box, text="Retirer", command=self.remove_item).pack(fill="x", pady=2)

        frame_opts = ttk.LabelFrame(tab_auto, text=" Options de Rognage des Bips (Début & Fin) ")
        frame_opts.pack(fill="x", **pad)

        self.var_trim_head = tk.BooleanVar(value=True)
        self.var_first_head = tk.BooleanVar(value=True)
        self.var_offset_head = tk.StringVar(value="2.0")

        self.var_trim_tail = tk.BooleanVar(value=True)
        self.var_last_tail = tk.BooleanVar(value=True)
        self.var_offset_tail = tk.StringVar(value="2.0")

        self.var_sox_norm = tk.BooleanVar(value=False)
        self.var_mkvmerge = tk.BooleanVar(value=False)
        self.var_format = tk.StringVar(value="flac")
        self.var_bits = tk.StringVar(value="24")
        self.var_out = tk.StringVar()

        # Row 0: Début
        ttk.Checkbutton(frame_opts, text="Couper bip DÉBUT", variable=self.var_trim_head).grid(row=0, column=0, sticky="w", **pad)
        ttk.Checkbutton(frame_opts, text="Aussi 1re bobine", variable=self.var_first_head).grid(row=0, column=1, sticky="w", **pad)
        ttk.Label(frame_opts, text="Offset après bip (s):").grid(row=0, column=2, sticky="e", **pad)
        ttk.Entry(frame_opts, textvariable=self.var_offset_head, width=6).grid(row=0, column=3, sticky="w", **pad)

        # Row 1: Fin
        ttk.Checkbutton(frame_opts, text="Couper bip FIN", variable=self.var_trim_tail).grid(row=1, column=0, sticky="w", **pad)
        ttk.Checkbutton(frame_opts, text="Aussi dernière bobine", variable=self.var_last_tail).grid(row=1, column=1, sticky="w", **pad)
        ttk.Label(frame_opts, text="Offset avant bip (s):").grid(row=1, column=2, sticky="e", **pad)
        ttk.Entry(frame_opts, textvariable=self.var_offset_tail, width=6).grid(row=1, column=3, sticky="w", **pad)

        # Row 2: Traitements additionnels
        ttk.Checkbutton(frame_opts, text="Normaliser le volume via SoX (Peak -0.1dB)", variable=self.var_sox_norm).grid(row=2, column=0, columnspan=2, sticky="w", **pad)
        ttk.Checkbutton(frame_opts, text="Muxer le résultat final dans un conteneur MKV via mkvmerge", variable=self.var_mkvmerge).grid(row=2, column=2, columnspan=2, sticky="w", **pad)

        # Row 3: Exportation
        ttk.Label(frame_opts, text="Format de sortie:").grid(row=3, column=0, sticky="w", **pad)
        fmt_combo = ttk.Combobox(frame_opts, textvariable=self.var_format, values=list(FORMATS.keys()), state="readonly", width=12)
        fmt_combo.grid(row=3, column=1, sticky="w", **pad)
        fmt_combo.bind("<<ComboboxSelected>>", self._on_format_change)

        ttk.Label(frame_opts, text="Résolution:").grid(row=3, column=2, sticky="e", **pad)
        ttk.Combobox(frame_opts, textvariable=self.var_bits, values=["16", "24"], state="readonly", width=6).grid(row=3, column=3, sticky="w", **pad)

        ttk.Label(frame_opts, text="Fichier de sortie:").grid(row=4, column=0, sticky="w", **pad)
        ttk.Entry(frame_opts, textvariable=self.var_out, width=65).grid(row=4, column=1, columnspan=2, sticky="we", **pad)
        ttk.Button(frame_opts, text="Parcourir...", command=self.browse_output).grid(row=4, column=3, **pad)

        frame_act = ttk.Frame(self)
        frame_act.pack(fill="x", **pad)

        self.btn_run = tk.Button(frame_act, text="▶ LANCER L'EXPORTATION ET LE PIPELINE CINÉMA", bg="#2d6a4f", fg="#ffffff", font=("Helvetica", 11, "bold"), command=self.start_process)
        self.btn_run.pack(side="left", fill="x", expand=True, padx=2)

        self.txt_log = tk.Text(self, bg="#111111", fg="#4ade80", font=("Consolas", 9), height=12)
        self.txt_log.pack(fill="both", expand=True, **pad)

    def _init_environment(self):
        self.log("=== Détection et auto-installation des logiciels ===")
        download_and_install_tools(self.log)
        
        ff = find_tool("ffmpeg")
        fp = find_tool("ffprobe")
        sox = find_tool("sox")
        mi = find_tool("MediaInfo")
        mkv = find_tool("mkvmerge")

        self.log(f"  • FFmpeg   : {'✓ Opérationnel (' + ff + ')' if ff else '❌ Absent'}")
        self.log(f"  • FFprobe  : {'✓ Opérationnel' if fp else '❌ Absent'}")
        self.log(f"  • SoX      : {'✓ Opérationnel' if sox else '⚠️ Option désactivée'}")
        self.log(f"  • MediaInfo: {'✓ Opérationnel' if mi else '⚠️ Option désactivée'}")
        self.log(f"  • mkvmerge : {'✓ Opérationnel' if mkv else '⚠️ Option désactivée'}")
        self.log("=========================================================\n")

    def log(self, text):
        self.msg_queue.put(("log", text))

    def _poll_queue(self):
        try:
            while True:
                kind, val = self.msg_queue.get_nowait()
                if kind == "log":
                    self.txt_log.insert(tk.END, val + "\n")
                    self.txt_log.see(tk.END)
                elif kind == "err_popup":
                    messagebox.showerror("Erreur", val)
                elif kind == "done":
                    self.btn_run.config(state="normal")
                    messagebox.showinfo("Succès", "Traitement et exportation terminés avec succès !")
        except queue.Empty:
            pass
        self.after(100, self._poll_queue)

    def add_paths(self, paths):
        fp = find_tool("ffprobe")
        mi = find_tool("MediaInfo")
        if not fp:
            messagebox.showerror("Outil Manquant", "ffprobe est introuvable.")
            return

        out_target = Path(self.var_out.get()).resolve() if self.var_out.get() else None

        for p in paths:
            path = Path(p)
            entries = sorted(path.iterdir()) if path.is_dir() else [p]
            for e in entries:
                if out_target and e.resolve() == out_target:
                    continue
                if e.suffix.lower() in DECODED_EXT and e not in self.files:
                    try:
                        info = probe_file(e, fp, mi)
                        self.infos[e] = info
                        self.files.append(e)
                        self.log(f"[Fichier Chargé] {e.name}")
                    except AudioProcessingError as err:
                        messagebox.showerror("Erreur", str(err))

        self.files.sort(key=natural_key)
        self.refresh_list()
        for m in check_reel_sequence(self.files):
            self.log("Attention : " + m)

    def refresh_list(self):
        self.lb.delete(0, tk.END)
        for f in self.files:
            info = self.infos.get(f)
            desc = info.describe() if info else ""
            self.lb.insert(tk.END, f"{f.name:<30} | {desc}")

    def show_mediainfo(self):
        sel = self.lb.curselection()
        if not sel:
            messagebox.showinfo("Info", "Sélectionnez une bobine.")
            return
        f = self.files[sel[0]]
        info = self.infos.get(f)
        if info and info.mediainfo_text:
            win = tk.Toplevel(self)
            win.title(f"Rapport MediaInfo - {f.name}")
            win.geometry("700x500")
            txt = tk.Text(win, bg="#1e1e1e", fg="#d4d4d4", font=("Consolas", 9))
            txt.pack(fill="both", expand=True)
            txt.insert(tk.END, info.mediainfo_text)
        else:
            messagebox.showwarning("Indisponible", "MediaInfo.exe n'a pas été trouvé.")

    def scan_beeps(self):
        ff = find_tool("ffmpeg")
        fp = find_tool("ffprobe")
        if not ff or not fp or not self.files:
            return
        
        self.log("\n=== Détection des bips d'amorce et de fin ===")
        off_h = float(self.var_offset_head.get().replace(",", "."))
        off_t = float(self.var_offset_tail.get().replace(",", "."))
        plan_trims(self.files, ff, fp, self.var_trim_head.get(), self.var_trim_tail.get(), off_h, off_t, self.var_first_head.get(), self.var_last_tail.get(), log=self.log)

    def add_files(self):
        p = filedialog.askopenfilenames(filetypes=[("Audio", "*.wav *.flac *.w64 *.mka"), ("Tous", "*.*")])
        if p:
            self.add_paths(p)

    def add_folder(self):
        d = filedialog.askdirectory()
        if d:
            self.add_paths([d])

    def autosort(self):
        self.files.sort(key=natural_key)
        self.refresh_list()

    def move_item(self, delta):
        sel = list(self.lb.curselection())
        if not sel:
            return
        for i in sel:
            j = i + delta
            if 0 <= j < len(self.files):
                self.files[i], self.files[j] = self.files[j], self.files[i]
        self.refresh_list()

    def remove_item(self):
        for i in reversed(self.lb.curselection()):
            f = self.files.pop(i)
            self.infos.pop(f, None)
        self.refresh_list()

    def clear_all(self):
        self.files.clear()
        self.infos.clear()
        self.refresh_list()
        self.log("[Info] Liste réinitialisée.")

    def _on_format_change(self, event=None):
        out_current = self.var_out.get()
        if out_current:
            fmt = self.var_format.get()
            ext = FORMATS[fmt][0]
            p = Path(out_current)
            self.var_out.set(str(p.with_suffix(ext)))

    def browse_output(self):
        fmt = self.var_format.get()
        ext = FORMATS[fmt][0]
        p = filedialog.asksaveasfilename(defaultextension=ext, filetypes=[(fmt.upper(), f"*{ext}")])
        if p:
            self.var_out.set(p)

    def start_process(self):
        if not self.files:
            messagebox.showwarning("Attention", "Veuillez ajouter des bobines audio.")
            return

        out_path = Path(self.var_out.get() if self.var_out.get() else "")
        if not out_path or str(out_path) == ".":
            self.browse_output()
            out_path = Path(self.var_out.get() if self.var_out.get() else "")
            if not out_path or str(out_path) == ".":
                return

        self.files = [f for f in self.files if f.resolve() != out_path.resolve()]
        self.refresh_list()

        self.btn_run.config(state="disabled")
        threading.Thread(target=self._run_async, daemon=True).start()

    def _run_async(self):
        try:
            ff = find_tool("ffmpeg")
            fp = find_tool("ffprobe")
            off_h = float(self.var_offset_head.get().replace(",", "."))
            off_t = float(self.var_offset_tail.get().replace(",", "."))
            
            self.log("\n[Bips] Analyse et planification des coupes (Début & Fin)...")
            plans = plan_trims(self.files, ff, fp, self.var_trim_head.get(), self.var_trim_tail.get(), off_h, off_t, self.var_first_head.get(), self.var_last_tail.get(), log=self.log)

            execute_pipeline(
                files=self.files,
                output=self.var_out.get(),
                fmt=self.var_format.get(),
                bits=int(self.var_bits.get()),
                use_sox=self.var_sox_norm.get(),
                use_mkvmerge=self.var_mkvmerge.get(),
                log=self.log,
                infos=plans
            )
            self.msg_queue.put(("done", None))
        except Exception as e:
            self.msg_queue.put(("err_popup", str(e)))
            self.log(f"\n[ERREUR] {e}")
            self.msg_queue.put(("done", None))

if __name__ == "__main__":
    app = ApplicationGUI()
    app.mainloop()
