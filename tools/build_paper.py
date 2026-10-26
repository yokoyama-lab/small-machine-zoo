#!/usr/bin/env python3
"""Build the short manuscript and the extended manuscript from one main text."""
from pathlib import Path
import shutil
import subprocess

root = Path(__file__).resolve().parents[1]
paper = root / 'paper'
out = root / 'out/paper'
out.mkdir(parents=True, exist_ok=True)
note = (paper/'note.tex').read_text()
marker = r'\begin{thebibliography}'
assert note.count(marker) == 1
full = note.replace(marker, '\\appendix\n'+(paper/'details.tex').read_text()+'\n'+marker)
date = r'\date{October 2026}'
assert full.count(date) == 1
full = full.replace(date, r'\date{October 2026\\Extended version}')
(out/'full.tex').write_text(full)
for name, source in [('note', paper/'note.tex'), ('full',out/'full.tex')]:
    for _ in range(2):
        result = subprocess.run(['pdflatex','-interaction=nonstopmode','-halt-on-error',
                                 '-output-directory='+str(out),str(source)], cwd=root,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        if result.returncode:
            print(result.stdout[-6000:])
            raise SystemExit(result.returncode)
    shutil.copy2(out/(name+'.pdf'),paper/(name+'.pdf'))
    print('Built paper/'+name+'.pdf')
