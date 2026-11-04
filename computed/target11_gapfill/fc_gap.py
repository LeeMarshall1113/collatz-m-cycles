"""Gap-fill driver: fastchain over all candidates at the given m, with the 72-point doubly computed B4 grid
(exactly as target11_referee/chain127_refB4only.py), but strictly single-process: multiprocessing.Pool is
replaced by an in-process serial map (same functions, same order of work; chunking as for procs=1).
usage: python fc_gap.py 112,113,115,...
"""
import sys, os
REL = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
sys.path.insert(0, os.path.join(REL, 'target11_referee'))
import chain127_refB4only as P   # noqa: E402  (unmodified referee pilot: grid selection + FC.run)
FC = P.FC


class SerialPool:
    def __init__(self, n, initializer=None, initargs=()):
        if initializer:
            initializer(*initargs)

    def __enter__(self):
        return self

    def __exit__(self, *a):
        return False

    def map(self, f, it, chunksize=1):
        return [f(x) for x in it]


FC.Pool = SerialPool

if __name__ == '__main__':
    sys.argv = [sys.argv[0], sys.argv[1], '1']
    P.main()
