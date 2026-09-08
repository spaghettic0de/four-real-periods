# Novelty audit — 2026-09-08

Status: strong evidence of a new four-task extension; no prior matching theorem located. This is a search record, not a proof of priority or a publication manuscript. Fable 5.1 independently reviewed the proof and novelty evidence; see verification-summary.md.

## Exact claim checked

Every four-task instance with positive real periods a_i and sum_i 1/a_i <= 5/6 admits S : Z -> Fin 4 such that every window of ceil(ell*a_i) consecutive days contains at least ell executions of task i, for every positive integer ell and every integer start. The Lean statement orders periods without loss of generality.

The extension to arbitrary task multiplicities with at most four distinct period values follows mathematically by aggregation followed by the established splitting lemma. This corollary is not yet formalized in the project.

## Decisive primary sources

1. Fujiwara, Miyagi and Ouchi, *Pinwheel Scheduling with Real Periods*, final journal PDF, published 2026-08-17: https://dmtcs.episciences.org/18808/pdf . Theorem 2 (PDF p.2) proves three distinct real values. Section 4 (PDF p.13) explicitly identifies extending the method to four or five distinct values as future work. The period semantics on p.2 match our all-window ceil(ell*a_i) semantics. The journal links arXiv v6, not the older v2 initially consulted: https://arxiv.org/html/2510.24068v6 (revised 2026-07-17). The current version retains the same scope and future-work statement.

2. Kawamura, *Proof of the Density Threshold Conjecture for Pinwheel Scheduling*, accepted PNAS version, arXiv v2 dated 2026-08-10: https://arxiv.org/html/2606.27104v2 . Theorem 1 explicitly restricts periods to integers. Immediately following it the author describes the noninteger extension as conjectured and confirmed for k <= 3. Section 2 gives the fractional-period semantics and weakening/splitting lemma. Thus the general integer theorem does not directly subsume ours.

3. Theorem 5 of the final Fujiwara et al. paper cites a sufficient real-period bound depending on the smallest period. It covers large-minimum-period instances, not all four-task instances at density 5/6. Theorem 4 covers two real period values at density <= 1.

4. Related scope checks: https://arxiv.org/abs/2510.06533 concerns the dual covering problem; https://arxiv.org/html/2602.11826v1 defines its combinatorial pinwheel application with integer deadlines; https://www.wild-inter.net/publications/gasieniec-smith-wild-2022.pdf treats integer-period Pareto surfaces. None of the statements inspected supplies this four-real-period result.

## Search coverage

General web/arXiv discovery queries included combinations of pinwheel scheduling with: real periods, fractional periods, non-integer, real-valued, four tasks, four-task, four periods, four distinct values, four distinct, 5/6, proof, theorem, Lean, formalization, Fujiwara, and 2026 September. Exact-title searches sought followups and citations. Author/database searches included Fujiwara's DBLP listing and Shinshu profile; the Shinshu page failed to open, so no full author-page audit is claimed. Indexed X searches for pinwheel proof and real-period scheduling did not locate a matching result; this is not an exhaustive X archive search.

Authenticated GitHub searches:

- Repositories: `pinwheel scheduling` returned a7kawamura/pinwheel_solver, Amelia-ka/pinwheel-scheduling-penalties, and roarin-roran/Towards-the-5-over-6-Density-Conjecture-of-Pinwheel-Scheduling.
- Repositories: `pinwheel real` returned no results.
- Code: `pinwheel language:Lean` returned no results.
- Code: `"real periods" pinwheel` returned no results.

The author's solver README describes integer inputs and links the packing and covering papers. Negative search results are limited by indexing, query matching, and repository visibility.

## Assessment and remaining limits

The latest directly relevant journal paper explicitly leaves the next case open, and the latest accepted general integer paper independently reports only the three-task real case. This is positive evidence for novelty, stronger than an unsuccessful exact-phrase search alone. We found no indexed public result that matches or implies the candidate theorem.

Appropriate claim: a Lean-checked four-task case of the real-period 5/6 conjecture that appears to extend the published three-value result. Do not claim to have solved the general real-period conjecture or the original integer conjecture. Do not assert that nobody has posted or privately proved it. Unindexed posts, private repositories, unpublished manuscripts, and concurrent work remain possible. No researchers have been contacted.

Proof validity is a separate question from novelty. The existing verification JSON records successful compilation of all ten modules and a final-module leanchecker pass. Fable 5.1 completed the review, rebuilt all ten modules, replayed each module, and replayed the import closure with --fresh. It passed the theorem and semantics, with publication corrections recorded in its review.
