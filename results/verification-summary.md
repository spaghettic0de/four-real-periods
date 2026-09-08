# Verification record

Fable 5.1 (`claude-fable-5-1`) independently reviewed the original ten proof modules on September 8, 2026. Its verdict was PASS on formal correctness and correspondence to the intended scheduling problem. It found no prior matching public result, while identifying the extension as anticipated by the original authors.

It rebuilt the modules from source, checked the source hashes, replayed each module, and replayed the final theorem's full import closure with `leanchecker --fresh`. The fresh replay reported a closure of 2,408 modules and 234,653 constants. It additionally reimplemented the rational coverage checks and tested malformed certificates.

The review identified these release corrections: explicitly state the sorted-input hypothesis; distinguish the unformalized multiplicity corollary; test the production certificate predicate; include per-module and fresh replays; correct stale status text; provide a proper pinned Lake project. Those corrections are incorporated in this package.

The original reviewed source hashes are in `pinwheel-lean-verification.json`. Reproducible release checks are recorded in `standalone-verification.json` after running `python3 experiments/verify.py`. Imported mathematical libraries and the Lean kernel remain part of the trust base. Independent AI review is not peer review.
