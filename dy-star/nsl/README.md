# NSL Example Illustrating DY*'s Assumptions

DY* assumes that methods execute atomically, without attacker interference, which significantly simplifies the formal reasoning.
This assumption is sound *only if* the code is structured such that each method contains at most a single protocol step.

This module contains a modified NSL example, which we have taken from DY* and adapted such that a single method (i.e., `initiator_send_msg_1_and_msg_3` in `NSL.Protocol.fst`) implements the protocol steps performed by the initiator. This violates DY*’s code structure assumptions, which let’s DY* unsoundly prove that the initiator receives a message without the responder sending it (because there is no corresponding send event on the trace between the two protocol steps of the initiator)! That is, either the initiator or the responder must have been corrupted. Since this reasoning applies to all possible executions of the protocol, we have proved that the NSL protocol cannot be executed without cooperation from the attacker, which is clearly not the case.

- `NSL.Protocol.fst` contains the initiator and responder implementations. The assert statement proving that the initiator or responder must have been corrupted is located on line 176.
- `NSL.Protocol.fsti` is the corresponding header file
- `NSL.SecurityProperties.fst` and `NSL.SecurityProperties.fsti` prove the same security properties for this NSL example as in the original NSL example by DY*.
- `NSL.Messages.fst` provides the definitions for protocol-specific events, functions for serializing and parsing messages, and the trace invariant.
- `NSL.Sessions.fst` provides the invariant for protocol-specific events and functions for serializing and parsing program state.
- `Makefile` verifies the example (see comments below)

## How To Verify
The entire folder is meant to be placed within a copy of DY*:
1. Clone DY*: `git clone https://github.com/REPROSEC/dolev-yao-star.git`
2. Change into the cloned directory (which we refer to as DY*'s root directory): `cd dolev-yao-star`
3. Checkout commit `ce75306`: `git checkout ce75306dc86a00970bd5136fda1d2009dba2096b`
4. Paste this folder into DY*'s root directory (similar to the existing NS, NSL, Signal, etc. examples). We assume next that the folder is still called `nsl`.
5. Follow the instructions to run the DY* docker image in the README in DY*'s root directory.
6. Switch to DY*'s root directory (within the docker container): `cd /home/build/dolev-yao-star`
7. Verify the DY* framework: `make`
    - In case this command fails with `cannot create directory ‘/.hints’: Permission denied`, add the following lines to the top of the Makefile in DY*'s root directory:
        ```
        FSTAR_HOME ?= /home/build/FStar
        DY_HOME ?= /home/build/dolev-yao-star
        ```

8. Switch into the subfolder containing this example (within the docker container): `cd nsl`
9. Verify this example (in subfolder `nsl` within the docker container): `make`
10. The second to last line of standard output should state: **`All verification conditions discharged successfully`**
