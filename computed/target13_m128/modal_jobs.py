"""Run independent exact table computations on Modal (CPU only).  Code is pinned: the needed directories of
computed/ are copied into the image at launch and their sha256 manifest is printed in every log.
usage:  modal run modal_jobs.py --jobs '<json list of [name, subdir, cpu, [args...]]>'
Each job: cd /root/computed/<subdir>; python <args...>; stdout+stderr returned and written to modal_logs/<name>.log."""
import json, os, hashlib, subprocess, time
import modal

HERE = os.path.dirname(os.path.abspath(__file__))
COMP = os.path.abspath(os.path.join(HERE, '..'))
DIRS = ['target1a', 'target7_threerise', 'target7b_push', 'target7b_referee', 'target10_rrise', 'target11_fourrise']

image = (modal.Image.debian_slim(python_version="3.12")
         .pip_install("numpy==2.2.6", "numba==0.61.2", "gmpy2==2.2.1", "mpmath==1.3.0")
         .env({"MPMATH_NOGMPY": "1"}))
for d in DIRS:
    image = image.add_local_dir(os.path.join(COMP, d), f"/root/computed/{d}",
                                ignore=["*.jsonl", "*.out", "*.log", "__pycache__", "*.txt"])
app = modal.App("collatz-m128-tables", image=image)


def manifest(root="/root/computed"):
    lines = []
    for d in DIRS:
        for f in sorted(os.listdir(os.path.join(root, d))):
            if f.endswith('.py'):
                h = hashlib.sha256(open(os.path.join(root, d, f), 'rb').read()).hexdigest()[:16]
                lines.append(f"{d}/{f} {h}")
    return "\n".join(lines)


def _run(name, subdir, args, nthreads):
    t = time.time()
    env = dict(os.environ, NUMBA_NUM_THREADS=str(nthreads), OMP_NUM_THREADS=str(nthreads))
    p = subprocess.run(["python"] + args, cwd=f"/root/computed/{subdir}", capture_output=True, text=True, env=env)
    head = f"# job {name}: python {' '.join(args)} (cwd {subdir}, {nthreads} threads)\n# code manifest:\n{manifest()}\n"
    return name, head + p.stdout + "\n# stderr:\n" + p.stderr + f"\n# exit {p.returncode} wall {time.time() - t:.0f}s\n"


@app.function(cpu=1.0, memory=2048, timeout=86400)
def run1(name, subdir, args):
    return _run(name, subdir, args, 1)


@app.function(cpu=4.0, memory=8192, timeout=86400)
def run4(name, subdir, args):
    return _run(name, subdir, args, 4)


@app.local_entrypoint()
def main(jobs: str):
    jl = json.loads(open(jobs).read() if os.path.exists(jobs) else jobs)
    os.makedirs(os.path.join(HERE, 'modal_logs'), exist_ok=True)
    calls = [((run4 if cpu >= 4 else run1).spawn(name, sub, args), name) for name, sub, cpu, args in jl]
    for c, name in calls:
        try:
            n, log = c.get()
        except Exception as e:
            n, log = name, f"# job {name} FAILED on Modal: {e!r}\n"
        open(os.path.join(HERE, 'modal_logs', f'{n}.log'), 'w').write(log)
        print(f"[{time.strftime('%H:%M:%S')}] done {n}: {log.strip().splitlines()[-1]}", flush=True)
