# flt-quad

Code to accompany the paper "Fermat's Last Theorem and modular curves over real quadratic fields" by Philippe Michaud-Jacobs.

The paper is available on arXiv here: https://arxiv.org/abs/2102.11699.
The published version of the paper is available here: https://doi.org/10.4064/aa210812-2-4.
The arXiv version of the paper contains corrections of minor computational errors that appeared in the published version.

The repository contains the following files (more description is contained within each file):

- formal_imm_74.m verifies the formal immersion criterion for X_0(74)
- irreducibility.m verifies part 1 of the irreducibility checks
- irreducibility_output.txt contains the output of the irreducibility.m file
- levels.m computes the possible levels N_p for Hilbert newforms
- levels_output.txt contains the output of the levels.m file
- modular_parametrisation.py verifies irreducibility using the modular parametrisation map
- newform_elimination.m carries out the newform elimination checks
- newform_elimination_output.txt contains the output of the newform_elimination.m file
- regular_primes.m contains functions for checking if primes are d-regular
- remaining_cases.m completes the elimination of newform steps
- remaining_cases_output.txt contains the output of the remaining_cases.m file
- sieves.m verifies the sieving computations

The code in this branch (main) of the repository differs from the version of the code originally associated with the published version of the paper (although the code is up to date with the current arXiv version). The notation in this branch matches that of the paper more closely, certain (minor) errors have been corrected, and more information and output has been included throughout. If you do wish to see the original code, it is available in the original-paper branch at the following link: https://github.com/michaud-jacobs/flt-quad/tree/original-paper.
