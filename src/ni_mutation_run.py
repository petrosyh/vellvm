#!/usr/bin/env python3
"""NI mutation-test driver (QuickChick-annotation aware, shell-out build).

The QuickChick CLI cannot drive our mutation testing: NITests.v shells out
to the prebuilt ./vellvm binary (Unix.open_process_in $VELLVM_BIN), so a
mutant in TaintTracker.v only matters once the binary is REBUILT — which the
quickChick tool does not do. This script mirrors the quickChick workflow
(parse (*! *) mutant annotations, run base + each mutant, report kills) but
activates each mutant by editing the source and running `make vellvm`.

Mutant annotation format (QuickChick convention) at a mutation site:

    (*! *)
    <correct code line(s)>            <- active by default
    (*!! mutant-name-1 *)
    (*! <mutant 1 code line(s)> *)    <- commented out by default
    (*!! mutant-name-2 *)
    (*! <mutant 2 code line(s)> *)
    ...

Activating mutant K: comment the correct lines, uncomment mutant K's code.
(Single-line correct + single-line mutant per entry — enough for binop.)

Usage (run from src/):
    python3 ni_mutation_run.py --list
    python3 ni_mutation_run.py [--file F] [--workers N] [--per P] [--timeout T]
A mutant is KILLED if the NI campaign reports any failure, SURVIVED if it
passes clean (→ candidate gap or equivalent mutant — investigate), or
BUILD-ERROR if `make vellvm` fails on it.
"""
import argparse, os, re, subprocess, sys, shutil, glob

def parse_sites(text):
    lines = text.split('\n')
    sites, i = [], 0
    while i < len(lines):
        if lines[i].strip() == '(*! *)':
            j = i + 1
            correct = []
            while j < len(lines) and not lines[j].strip().startswith('(*!!'):
                correct.append(j); j += 1
            muts = []
            while j < len(lines) and lines[j].strip().startswith('(*!!'):
                name = lines[j].strip()[4:].strip()
                if name.endswith('*)'): name = name[:-2].strip()
                code_line = lines[j+1]
                m = re.match(r'(\s*)\(\*!(.*)\*\)\s*$', code_line)
                muts.append({'name': name, 'code': m.group(2).strip(),
                             'indent': m.group(1), 'code_idx': j+1})
                j += 2
            for mu in muts:
                sites.append({'correct_idx': list(correct), 'mut': mu})
            i = j
        else:
            i += 1
    return lines, sites

def make_mutant_text(lines, site):
    out = list(lines)
    for k in site['correct_idx']:
        out[k] = re.sub(r'(\S.*)', r'(* \1 *)', out[k], count=1)
    mu = site['mut']
    out[mu['code_idx']] = mu['indent'] + mu['code']
    return '\n'.join(out)

def run(cmd, **kw):
    return subprocess.run(cmd, shell=True, capture_output=True, text=True, **kw)

def build():
    r = run("make rocq/NI/TaintTracker.vo && make vellvm")
    return r.returncode == 0

def ni_campaign(outdir, workers, per, timeout):
    shutil.rmtree(outdir, ignore_errors=True)
    r = run(f"./run_ni_parallel.sh {workers} {per} {timeout} {outdir} 3")
    killed = bool(re.search(r'FAILURES found', r.stdout))
    total = re.search(r'TOTAL\s+passed=(\d+)\s+discards=(\d+)\s+failed=(\d+)', r.stdout)
    summ = total.group(0) if total else r.stdout[-300:]
    # tests-to-kill: min "Failed after N" across worker logs (if any killed)
    ttk = []
    for log in glob.glob(f"{outdir}/run_*.log"):
        m = re.findall(r'Failed after (\d+) tests', open(log, errors='replace').read())
        ttk += [int(x) for x in m]
    if ttk:
        summ += f"  | tests-to-kill: min={min(ttk)} (n={len(ttk)} workers killed)"
    return killed, summ

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--file', default='rocq/NI/TaintTracker.v')
    ap.add_argument('--workers', type=int, default=4)
    ap.add_argument('--per', type=int, default=300)
    ap.add_argument('--timeout', type=int, default=2)
    ap.add_argument('--list', action='store_true')
    ap.add_argument('--only', default='',
                    help='comma-separated mutant names to run (default: all)')
    ap.add_argument('--outroot', default=os.path.expanduser('~/ni_mut'))
    a = ap.parse_args()

    orig = open(a.file).read()
    lines, sites = parse_sites(orig)
    if a.list:
        for s in sites: print(s['mut']['name'], '->', s['mut']['code'])
        return
    if a.only:
        want = set(x.strip() for x in a.only.split(',') if x.strip())
        sites = [s for s in sites if s['mut']['name'] in want]
        missing = want - {s['mut']['name'] for s in sites}
        if missing: sys.exit(f"unknown mutant(s): {sorted(missing)}")
    if not sites:
        sys.exit("no (*! *) mutation sites found")

    results = []
    try:
        for s in sites:
            name = s['mut']['name']
            print(f"\n===== mutant: {name}  (code: {s['mut']['code']}) =====", flush=True)
            open(a.file, 'w').write(make_mutant_text(lines, s))
            if not build():
                results.append((name, 'BUILD-ERROR', ''));
                print(f"  {name}: BUILD-ERROR", flush=True); continue
            killed, summ = ni_campaign(f"{a.outroot}_{name}", a.workers, a.per, a.timeout)
            verdict = 'KILLED' if killed else 'SURVIVED'
            results.append((name, verdict, summ))
            print(f"  {name}: {verdict}  [{summ}]", flush=True)
    finally:
        open(a.file, 'w').write(orig)   # always restore correct source
        build()                          # rebuild baseline

    print("\n==================== MUTATION SUMMARY ====================")
    for name, verdict, summ in results:
        print(f"  {verdict:11s} {name:22s} {summ}")
    nkill = sum(1 for _,v,_ in results if v == 'KILLED')
    print(f"  ---- {nkill}/{len(results)} killed ----")
    print("  (source restored to correct + baseline rebuilt)")

if __name__ == '__main__':
    main()
