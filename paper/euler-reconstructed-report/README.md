# A Verified WebAssembly Solver for a Two-Dimensional Euler Riemann Problem

This report documents the completed reconstructed Euler solver, its exact-binary execution and numerical theorems, and the 192 × 192 and 800 × 800 calculations.  The manuscript includes both final density and pressure images.  Its evidence checkpoint is `73e5b54ee6ba398cdd4d42feadc42e2c6ec5a33a`.

The [reviewed PDF](v6/pass-02/main.pdf) has 15 pages and includes both final density and pressure figures.  Its [manuscript source](v6/main.tex), [extracted metadata](v6/metadata.json), [review record](review.md), and [publication record](publication-record.md) preserve the submission evidence.  marXiv accepted the final report as [2609.00006v4](http://127.0.0.1:8405/abs/2609.00006v4), with no editorial remarks.  Its submission identifier is `661f900da98f`.  Public static export is off.

Section 5.2 gives the end-to-end proof composition: embedded bytes, checked decoding and validation, execution-model equality, termination, the returned array, and the numerical postconditions.  It distinguishes application status zero from interpreter success and states the assumptions for the observed computation and image.  The report also covers physical hyperbolicity and conservation, reconstruction and speed counterexamples, comparison with Lanyon, and remaining convergence obligations.  Preparation preserves the completed proofs, simulation data, earlier reports, and every build pass.

## Build and review

The report uses the installed TeX Live packages.  Build from the repository root into a fresh directory with `pdflatex -interaction=nonstopmode -halt-on-error -output-directory=NEW_DIRECTORY paper/euler-reconstructed-report/v6/main.tex`.  A second pass needs the first pass's auxiliary file to resolve references.  The final submitted build has no warnings, undefined references, or overfull boxes.  Its PDF SHA-256 is `88d4f024626722462ea622ccda871ee8f1ec261f6c6cd42822df56b9bf0b4eba`.
