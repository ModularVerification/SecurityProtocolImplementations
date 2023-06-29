# Concise Snippet Illustrating DY*'s Assumptions

DY* assumes that methods execute atomically, without attacker interference, which significantly simplifies the formal reasoning.
This assumption is sound *only if* the code is structured such that each method contains at most a single protocol step.

This module shows a concise example (in `RecvSentMsg.fst`) violating DY*’s code structure assumptions, which let’s DY* unsoundly prove properties that do not hold under a Dolev–Yao attacker.

- `RecvSentMsg.fst` contains the actual code snippet
- `RecvSentMsg.fsti` is the corresponding header file
- `RecvSentMsgDefinitions.fst` provides the definition of the trace invariant
- `Makefile` verifies the snippet (see comments below)

## How To Verify
The entire folder is meant to be placed within a copy of DY*:
1. Clone DY*: `git clone https://github.com/REPROSEC/dolev-yao-star.git`
2. Change into the cloned directory (which we refer to as DY*'s root directory): `cd dolev-yao-star`
3. Checkout commit `ce75306`: `git checkout ce75306dc86a00970bd5136fda1d2009dba2096b`
4. Paste this folder into DY*'s root directory (similar to the existing NS, NSL, Signal, etc. examples). We assume next that the folder is still called `snippet`.
5. Follow the instructions to run the DY* docker image in the README in DY*'s root directory.
6. Switch to DY*'s root directory (within the docker container): `cd /home/build/dolev-yao-star`
7. Verify the DY* framework: `make`
    - In case this command fails with `cannot create directory ‘/.hints’: Permission denied`, add the following lines to the top of the Makefile in DY*'s root directory:
        ```
        FSTAR_HOME ?= /home/build/FStar
        DY_HOME ?= /home/build/dolev-yao-star
        ```

8. Switch into the subfolder containing this snippet (within the docker container): `cd snippet`
9. Verify this snippet (in subfolder `snippet` within the docker container): `make`
10. The second to last line of standard output should state: **`All verification conditions discharged successfully`**
