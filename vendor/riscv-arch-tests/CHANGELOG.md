# CHANGELOG

## [3.6.2] - 2023-02-08
- Remove RV64IB from ISA list of zext test. 

## [3.6.1] - 2023-01-28
- Fix satp restore condition.

## [3.6.0] - 2023-01-26
  - Removed the bugs in RVTEST_GOTO_LOWER_MODE macro
  - Removed the bugs in RVTEST_GOTO_MMODE macro and defined strap_routine directive.
  - Updated RVTEST_TRAP_SAVEAREA and RVTEST_TRAP_EPILOG macros to refine the definitions of per mode save area macros.
  - Added better indications of when the trap signature area is overrun
  - Ensured that the trap handler keeps the trampoline 64B aligned (need for CLIC spec)
  - fixed the handling of when xTVEC was not initialized and also could not be written
  - rewritten the save_GPR macro to it now compiles
  - some miscellaneous optimizations

## [3.5.3] - 2022-11-22
  - Fix Canary definition according to sigalign.
  - Fix SIGALIGN definition.
  - Fix inconsistencies in tests.
  - Add Zicsr to ISA in RV32 privilege tests
  - Modify signature size requirement to multiple of 4.

## [3.5.2] - 2022-11-25
  - adding a pull request template
  - removed riscv-test-stats directory and migrated those to a gdrive folder [here](https://drive.google.com/drive/folders/1KBRy6OgxnOPTDgyfJDj0gcMi5VdMLtVo?usp=share_link)
  - updated contribution guide on steps to done to upload test stats for PRs

## [3.5.1] - 2022-10-28
  - Add test cases for P-ext
  - Correct TEST_PKRR_OP() macro in arch_test.h 
  - Avoid reusing RVTEST_SIGUPD_FID() for P-ext macros: SIGALIGN may not be defined when FLEN==0

## [3.5.0] - 2022-10-17
- Add Canaries (labels - sig_begin_canary. tsig_begin_canary, tsig_end_canary, sig_end_canary)
- Signature boundary labels (rvtest_sig_begin and rvtest_sig_end) (enables the new trap handler to fix #262)
- Zicsr ISA update for priv tests (#233)
- Default data section should be 16 bytes. This expands default rvtest_data region to be at least 16 bytes (#211)
- Replace la/li ops with LA/LI macros in tests (#275)
- Remove trap handler enable macro from misalign1-jalr tests (#281)
- Move misalign1-jalr test into I directory. (#281)
- Move fmem tests into the [F|D]/src directory
- Fix correctval in tests to ?? instead of 0. (#256)
- Remove the riscv-target directory (#259)
- Fix the store instruction used in 64bit K tests from `sw` to `SREG` (#282)

## [3.4.1] - 2022-09-11
  - Fix trailing space in arch_test.h

## [3.4.0] - 2022-08-18
  - Added tests for Bitmanip and Crypto scalar extensions
  
## [3.3.0] - 2022-08-08
  - Added floating point aligned memory operations tests.


## [3.2.1] - 2022-08-01
  - Fix invalid link in README.adoc

## [3.2.0] - 2022-07-19
  - Add definition of LREGWU according to XLEN.
  - Fix corresponding fcvt.\*.wu tests.

## [3.1.1] - 2022-07-07
  - Fix definition of FPID macro to add load instruction.
  - Fix nan boxing macro to use correct endianness.

## [3.1.0] - 2022-07-05
  - Update floating point tests and macros to ensure flags are cleared & correct rounding modes are used.

## [3.0.1] - 2022-05-13
  - Rename "master" to "main" in github-action yamls

## [3.0.0] - 2022-05-07
  - Migration of test-suite to new RISCOF framework.

## [2.7.4] - 2022-04-18
  - Clean fflags in F* macros
  - Update rv32i_m/F and rv64i_m/D signatures

## [2.7.3] - 2022-03-31
  - Update framework to support test suite compilation with LLVM.

## [2.7.2] - 2022-03-18
  - Add sigalign based changes to F&D sigupd macros.
  - Add helper macro to check offset legality.

## [2.7.1] - 2022-03-18
  - Fix bug in auto-offset update for SIGUPD macros.

## [2.7.0] - 2022-03-15
  - Updated K Crypto (Scalar) instructions for the V.1.0.0 ratified spec.
  - changed xperm.n -> xperm4 and xperm.b -> xperm8 instructions 
  - removed unsupported packu

## [2.6.3] - 2022-03-04
  - import and synchronize P-ext changes in arch_test.h from riscv-ctg
  - automatically adjust base and offset if offset gets too big

## [2.6.2] - 2022-02-24
  - modified verify.sh to ignore comments in reference signature during diff operation [#230]
  - udpated test-format spec to include the order of lines in the signature file [#214]
  - RVTEST_E macro to be enabled for all rv32E tests. [#227]

## [2.6.1] - 2021-11-25
  - Fixed RVTEST_FP_ENABLE macro for the issue #223

## [2.6.0] - 2021-10-21
  - Added rv64d tests, references, coverage files and data propagation reports
  - removed unwated re-assignment of macros for RV64F combination in `arch_test.h`
  - fixed rvtest-case strings for flw and fsw tests in rv32if suite

## [2.5.4] - 2021-10-20
  - Second Fix for the issue #206

## [2.5.3] - 2021-10-15
  - fix the lower case `i` in the `RVTEST_CASE` macros used in the shift operation tests.

## [2.5.2] - 2021-10-14
  - update format for aes32 and sm4 instructions
  - update reference signature for sha256 and sm3 instructions in rv64i_m/K_unratified
  - delete zip and unzip tests in rv64i_m/K_unratified
  - update tests for aes64ks1i, sm4ed and sm4ks to use byte_count with overlap = "Y" to improve the coverage of S-boxes

## [2.5.1] - 2021-10-07
  - added styles files to the F coverage report directories.

## [2.5.0] - 2021-10-01
  - Added rv32f tests, references, coverage files and data propagation reports
  - fixed broken links in READMEs across the repo.
  - corrected string "EBREAK" in io string macro to "ECALL" for ecall.S tests. #207
  - fixed typo `.alive` --> `.align` in `riscv-target/example_target/model_test.h`.

## [2.4.7] - 2021-10-01
  - Fix for the issue #206

## [2.4.6] - 2021-08-02
  - Added rv32e tests in riscv-test-suite
  
## [2.4.5] - 2021-07-29
  - fix for issue #195

## [2.4.4] - 2021-07-19
  - Annotating tags during releases

## [2.4.3] - 2021-05-20
  - added new 64-bit K crypto tests as per the test-plan presented by the scalar crypto task group
    [here](https://github.com/riscv/riscv-crypto/blob/d89dfee25780f79c162da4eb69cd9076dd701c88/tests/compliance/test-plan-scalar.adoc)
  - added new 32-bit K crypto tests as per the above mentioned test-plan.
  - added coverage and data propagation reports for the above tests.
  - updated README in riscv-test-suite
  - added missing semi-colon in example target Makefile.include files

## [2.4.2] - 2021-04-20
  - changed all occurances of SPTBR to the new name SATP

## [2.4.1] - 2021-04-01
  - updated issue number in TestFormatSpec to be consistent with doc history
  - adding a contribution guideline
  - updated comment on usage of RISCV_DEVICE in Makefile.include
  - updated licenses that are currently used by tests
  - renamed K tests to K_unratified
  - updated ci to build and upload pdf for testformatspec

## [2.4.0] - 2021-03-26
2021-03-26 Duncan Graham <info@imperas.com>
	- Added new K Crypto (scalar) (0.8.1) tests from Imperas

## [2.3.1] - 2021-03-20
### Changed
  - Compliance Task Group changed to Architecture Test SIG in all docs and comments
  - replacing old riscv-compliance link with new riscv-arch-test links
  - fixed ci for release
### Removed
  - spec/TestFormatSpec.pdf is removed since its old. Keeping only adoc file
  - removing obsolete and commented out portions from doc/README

## [2.3] - 2021-03-11
### Added
	- updated maintainers list in root-level readme
	- updated the links to riscof, isac and ctg repos and docs in root-level readme
	- adding CI to update versions automatically
### Removed
	- replaced spike target with a REAMDE pointing to riscv-isa-sim/arch_test_target/README.md

## [2.2] - 2021-01-28
	2021-01-22 Tobias Wölfel <tobias.woelfel@mailbox.org>
		* Add missing base ISA check in riscv-test-suite
	
	2021-01-20 Xiretza <xiretza@xiretza.xyz>
		* Deduplicate makefiles in riscv-test-suite
		* Makefile: Fix ordering of simulate and verify targets to allow multi-job runs (make -j)
		* Makefile.include: Document RISCV_TEST
		* Makefile: use $(TARGETDIR) variable for postverify target instead of hard-coded path
	
	2021-01-16 S Pawan Kumar <spawan1999@gmail.com>
	  	* Fixed NARGS macro defintion to work correctly. 
	
	2021-01-15 Xiretza <xiretza@xiretza.xyz>
		* style: Add a missing space to the "OK" message in verify.sh
	
	2020-12-17 Neel Gala <neelgala@incoresemi.com>
	  * remove env folder symlinks from all riscv-test-suite src folders 
		* fixed assertion macros for ovpsim
		* renamed RVTEST_ASSERT to RVMODEL_ASSERT in the Makefile and ovpsim macros
		* tests updated with right set of "correctvals"
	
	2020-11-24 Neel Gala <neelgala@incoresemi.com>
		* added MIGRATION.adoc in doc directory to indicate how old framework targets can work with
		  changes made as part of this PR
		* updated doc/README.adoc to avoid the word "compliance" and updated the section on porting a new
		  target to the framework.
		* Added an example_target directory to host dummy files which can be used as a starting point for
		  porting targets. This was provided by MarcKarasek.
		* migrated/ported existing targets (except codasip and sifive-formal) to the new framework
		  changes.
		* in riscv-test-env/p/riscv_test.h changed names of RVTEST_[CODE/DATA]_[BEGIN/END] to
		  RVTEST_[CODE/DATA]_[BEGIN/END]_OLD respectively to avoid conflicts with the new framework macros.
		* in riscv-test-env/p/riscv_test.h re-strutucture RVTEST_DATA_BEGIN_OLD/END to ensure that all
		  target specific data contents are introduced in RVTEST_DATA_END after the signature.
		* added new file riscv-test-suite/env/arch_test.h which contains the macros used by the new set of 
		  tests. A symlink to this in the riscv-test-env directory is also created. The arch_test also 
		  includes aliases for the old macros. 
		* encoding.h moved to riscv-test-suite/env and a symlink to this file exists in riscv-test-env.
		  This was done to ensure that the arch_test.h and encoding.h are not to be modified by the
		  targets
		* Added riscv-test-stats which includes coverage and data propagation reports for the tests
		  available in the riscv-test-suite directory.
		* upddted the directory structure of the riscv-test-suite as per definition found in the
		  TestFormatSpec document.
		* new set of tests with better coverage for rv[32/64][I,M,C, Zifencei] added. Almost all tests 
			were generated using the open source riscv_ctg tool. A few tests like fence, fencei, ebreak, 
			ecall, etc were handwritten/modified to follow the new macro conventions.
		* Updated TestFormatSpec to avoid the word compliance and also updated the definitions of macros
		  and signatures
		* created a root-level Makefile.include to decouple the Makefile and target specific settings. 
		* Added riscv-target and Makefile.include to the .gitignore file to stop tracking target specific
		  changes.
		* Added special targets for compile(build), simulate(run) and verify in the Makefiles of each
		  test-suite.
		* the existing riscv-targets have been either updated for the new framework or migrated to the
			framework.
	
	2020-10-15 Simon Davidmann <simond@imperas.com>
	    * riscvOVPsim enhanced and moved to its own respository: github.com/riscv-ovpsim
	
	2020-04-24 Allen Baum <allen.baum@esperantotech.com>
		* fixed the I-SB-01.S and I-SH-01.S tests and associated reference signatures to account
		of tests with negative offsets (which causes stores outside the signature area)
	  
	2020-03-19 Neel Gala <neelgala@gmail.com>
	    * restructuring the riscv-test-suite to indicate clearly what is deprecated, wip and usable
	      tests.
	    * based on the above fixed the directory structure for riscv-targets where-ever applicable. Only
	      tested riscvOVPsim and spike.
	    * fixed script bugs for spike as well
	    * renamed rv32i/I-IO.S to rv32i/I-IO-01.S along with necessary changes to the reference files
	      and Makefrag
	    * renamed mbadaddr csr to mtval as raised in issue #31
	    * C.SWSP-01.S test updated to fix issue #37
	
	2020-03-18 Neel Gala <neelgala@gmail.com>
	    * fixed doc/README.adoc with correct version to pass the sanity-check in the doc/Makefile
	
	2020-02-07 Prashanth Mundkur <prashanth.mundkur@gmail.com>
	    * Support F extension on RV32 sail-riscv-c.
	
	2019-12-01 Allen Baum <allen.baum@esperantotech.com>
	        * modified macro names to conformn to riscof naming convention of model specific vs. pre-defined
		* add more complete list of macros, their uses, parameters, and whether they are required or optional
		* minor structural changes (moving sentences, renumbering) and typo fixes
		* clarified impact of debug macros
		* clarified how SIGUPD and BASEUPD must be used
	        * remove section about test taxonomy, binary tests, emulated ops
	        * clarify/fix  boundary between test target and framework responsibilities
		   (split test target into test target and test shell)
	        * remove To Be discussed items that have been discussed
		* remove default case condition; if conditions are unchanged, part of same case
	        *  minor grammatical changes related to the above
	
	2019-10-16 Allen Baum <allen.baum@esperantotech.com>
		* spec/TestFormatSpec.adoc: changed the format of the signature to fixed physical address size, fixed 32b data size extracted from COMPLIANCE_DATA_BEGIN/END range.
	
		* more gramatical fixes, clarifications added
		* added To Be Discussed items regarding emulated instruction and binary tests
	
	2019-09-11 Allen Baum <allen.baum@esperantotech.com>
		* spec/TestFormatSpec.adoc:   more grammar and typo corrections and changes
		  clarified and added To Be Discussed issues
	
	2019-09-11 Allen Baum <allen.baum@esperantotech.com>
	    * spec/TestFormatSpec.adoc:   many grammar and typo corrections and changes
		removed many "to Be Discussed items and made them official
		Added wording to clarify spec intent (work in progress/goal rather than final)
		Added macros to ease test authoring: RVTEST_SIGBASE, RVTEST_SIGUPDATE, RVTEST_CASE
		Added detail on proposals for connection to framework (how framework selects tests).
		Expanded definition of signature format
		Changed the (proposed) directory structure and naming convention to eliminate ambiguities, add consistancy and slightly better match existing structure
		Added many "future work" items related to the above
		Added examples and comments to code examples to indicate how proposed macros would be used
	   * .gitignore: added condition to ignore Mac file system artifacts
	
	
	2019-11-05 Lee Moore <moore@imperas.com>
	    * Restructured RV32I to move Zicsr and Zifencei into their own suites
	
	2019-10-14 Lee Moore <moore@imperas.com>
	    * Added Ability to run a single test by using the Make Variable RISCV_TEST
	    for example, to only run the test I-ADD-01 from the rv32i suite
	        make RISCV_ISA=rv32i RISCV_TEST=I-ADD-01
	    * Added Top Level Variable to Makefile RISCV_TARGET_FLAGS, 
	    in the case of the RISCV_TARGET this can be passed and appended to the invocation
	    commandline configuration, for example to pass a command line flag to the RISCV_TARGET
	    to perform tracing. The value of this flag will be target specific
	        make RISCV_ISA=rv32i RISCV_TEST=I-ADD-01 RISCV_TARGET_FLAGS="--trace"
	    This is has also been added to all other targets to allow target configuration from
	    the commandline
	
	2019-10-07 Philipp Wagner <phw@lowrisc.org>
	    * When executing the test suite, Ibex always writes an instruction
	      log. Update the Makefile to write it to a test-specific location
	      (next to all other log files).
	    * On Ibex, provide an additional .objdump-noalias disassembly file
	      with no aliases and numeric register names (instead of ABI names).
	      This file matches the Ibex trace and can be used to debug the test
	      runs.
	
	2019-08-29 Robert Balas <balasr@iis.ee.ethz.ch>
	    * Added support for using RI5CY as a target.
	    * Added subdirectory riscv-target/ri5cy
	
	2019-08-08 Lee Moore <moore@imperas.com>
	    * Added support for lowRISC/ibex RTL as a target using Verilator.
	      In conjunction with Philipp Wagner of lowRISC phw@lowrisc.org
	
	2019-07-18 Paul Donahue <pdonahue@ventanamicro.com>
	    * Fix typos/grammar and use correct architectural terms.
	
	2019-06-21 Ben Selfridge <benselfridge@galois.com>
	    * Added support for using the the GRIFT simulator as a target.
	    * Added subdirectory riscv-target/grift
	    * updated README.md and doc/README.adoc
	
	2019-05-23 Prashanth Mundkur <prashanth.mundkur@gmail.com>
	    * Added support and instructions for using the C and OCaml simulators from the Sail RISC-V formal model as targets.
		* added subdirectories riscv-target/sail-riscv-c and riscv-target/sail-riscv-ocaml
		* updated README.md and doc/README.adoc
	
	2019-04-05 Allen Baum <allen.baum@esperantotech.com>
	    * spec/TestFormatSpec.adoc:  Adding details, minor corrections, ToBeDiscussed
	      items and clarifications to the specification of the future compliance test
	      suite. Also removing restrictions on having absolate addresses in signature
	
	2019-02-21 Lee Moore <moore@imperas.com>
	    * Fixed     bug in RVTEST_IO_ASSERT_GPR_EQ which was not preserving register t0
	    * Corrected commit I-LUI-01.S, register target changed but missed assertion
	
	2019-02-21 Deborah Soung <debs@sifive.com>
	    * added RiscvFormalSpec as a target with its own unique environment
	
	2019-02-15 Radek Hajek <radek.hajek@codasip.com>
	    * updated rv32i tests to support all registers (x31) with assertions
	    * updated spec/TestFormatSpec.adoc example ISA test with new assertions
	
	2019-02-05 Deborah Soung <debs@sifive.com>
	    * [Issue #33] fixing rv32si/ma_fetch.S test
	    * [Issue #32] fixing breakpoint test
	
	2019-02-01 Lee Moore <moore@imperas.com>
	    * updated Infrastructure macros to support non-volatile registers
	    * updated riscvOVPsim
	
	2019-01-29 Deborah Soung <debs@sifive.com>
	    * Added Rocket Chip generated cores as a target
	        * riscv-target/rocket/compliance_io.h created
		* riscv-target/rocket/compliance_test.h created
		* riscv-target/rocket/*/Makefile.include created for existing test suites
		* README.adoc updated with instructions for using Rocket cores as targets
		
	2019-01-22 Premysl Vaclavik  <pvaclavik@codasip.com>
	    * feature: initial version of Compliance Test Format Specification
	        * This new document outlines how we should like the compliance
	          system to work going forward. By contrast the doc/README.adoc file
	          describes the current system as it is.
	        * Approved at Compliance TG meeting of 9 Jan 2019.
	
	2019-01-02 Radek Hajek <radek.hajek@codasip.com>
	    * unified macros in all compliance tests
	
	2018-12-20 Lee Moore <moore@imperas.com>
	    * fixed riscvOVPsim 
	
	2018-11-22 Simon Davidmann <simond@imperas.com>
	    * added information on test suite status
	    
	2018-11-21 Olof Kindgren <olof.kindgren@gmail.com>
	    * Added support for using external target directories with $TARGETDIR
	
	2018-11-21 Neel Gala <neelgala@incoresemi.com>
	   	* riscv-test-suite/rv_/references/_.reference_output: changed signature 
		  format for all tests to include only 4-bytes per line starting with the
	  	  most significant byte on the left.
	    	* riscv-target/spike/device/rv_/Makefile.include: Added a patch for 
		  spike-device Makefiles where the old-signature format is post-processed 
	      	  to generate a signature in the new format at the end of each test.
		* riscv-target/riscvOVPsim/device/rv_/Makefile.include: same patch as above.
	    	* Makefile: default target for Makefile is now to run all tests supported by 
		  the target mentioned defined by RISCV_TARGET variable.
	
	2018-10-11 Simon Davidmann <simond@imperas.com>
	    * Ported github riscv/riscv-tests for RV32 processors to this compliance env
	    * rv32ua rv32uc rv32ud rv32uf rv32ud rv32ui
	
	2018-09-10  Lee Moore  <moore@imperas.com>
		* Added tests to RV32I to improve coverage, usage of Imperas Mutating Fault Simulator to 
		  identify untested usage cases
		* Macro renames to support GPR, (S)FPR, (D)FPR
		* Added test suite RV32IM to test 32 bit Multiply and Divide instructions 
		* Added test suite RV32IMC to test 32 bit Compressed instructions
		* Added test suite RV64I to test 64 bit Integer instructions
		* Added test suite RV64IM to test 64 bit Multiply and Divide instructions 
		
		
	2018-06-15  Radek Hajek  <hajek@codasip.com>
	
		Modifications to support Codasip simulator.
	
		The simulator is renamed as Codasip-simulator (was
		Codasip-IA-simulator), compliance_test.h has been moved to target
		directories and a COMPILE_TARGET has been added to Makefile to
		allow use of LLVM.
	
		* Makefile: Include Codasip simulator target.
		* riscv-target/codasip-IA-simulator/compliance_io.h: Renamed as
		riscv-target/Codasip-simulator/compliance_io.h.
		* riscv-target/Codasip-simulator/compliance_io.h: Renamed from
		riscv-target/codasip-IA-simulator/compliance_io.
		* riscv-target/Codasip-simulator/compliance_test.h: Created.
		* riscv-target/codasip-IA-simulator/device/rv32i/Makefile.include:
		Renamed as
		riscv-target/Codasip-simulator/device/rv32i/Makefile.include
		* riscv-target/Codasip-simulator/device/rv32i/Makefile.include:
		Renamed from
		riscv-target/codasip-IA-simulator/device/rv32i/Makefile.include.
		* riscv-test-env/compliance_test.h: Renamed as
		riscv-target/riscvOVPsim/compliance_test.h.
		* riscv-target/riscvOVPsim/compliance_test.h: Renamed from
		riscv-test-env/compliance_test.h.
		* riscv-target/riscvOVPsim/device/rv32i/Makefile.include: Updated
		for new environment.
		* riscv-target/spike/compliance_test.h: Created.
		* riscv-target/spike/device/rv32i/Makefile.include: Updated for
		new environment.
		* riscv-test-suite/rv32i/Makefile: Likewise.
	
	2018-06-10  Jeremy Bennett  <jeremy.bennett@embecosm.com>
	
		Put placeholders in empty directories to make sure they show in
		the GitHub hierarchy.
	
		* riscv-test-suite/rv32i/.gitignore: Created.
		* riscv-test-suite/rv32m/.gitignore: Created.
	
	2018-06-10  Jeremy Bennett  <jeremy.bennett@embecosm.com>
	
		* README.md: Make references to files in the repo into links.
	
	2018-06-09  Jeremy Bennett  <jeremy.bennett@embecosm.com>
	
		* .gitignore: Ignore editor backup files.
	
	2018-06-09  Jeremy Bennett  <jeremy.bennett@embecosm.com>
	
		* README.md: Add better link to documentation README.md.
	
	2018-06-08  Jeremy Bennett  <jeremy.bennett@embecosm.com>
	
		* README.md: Move AsciiDoc details into new README.md in the doc
		directory.
	
	2018-06-08  Jeremy Bennett  <jeremy.bennett@embecosm.com>
	
		* README.md: Fix typo in link to AsciiDoc cheat sheet
	
	2018-06-08  Jeremy Bennett  <jeremy.bennett@embecosm.com>
	
		* COPYING.BSD: Created.
		* COPYING.CC: Created.
		* README.md: Add git process, licensing and engineering process.
	
	2018-06-08  Jeremy Bennett  <jeremy.bennett@embecosm.com>
	
		* README.md: Correct details for running the compliance tests and
		directory for OVPsim.
	
	2018-06-08  Jeremy Bennett  <jeremy.bennett@embecosm.com>
	
		Clean restructuring to just the work of interest.
	
		* thought-experiments: Directory removed.
		* .gitignore: Merged with TestStructure/.gitignore
		* Makefile: Renamed from TestStructure/Makefile.
		* TestStructure/Makefile: Renamed as Makefile.
		* README.md: Merged with TestStructure/README.md.
		* TestStructure/.gitignore: Deleted and contents moved into
		.gitignore.
		* TestStructure/README.md: Deleted and contents moved into
		README.md.
		* TestStructure/doc: Directory deleted.
		* TestStructure/riscv-target: Directory moved to riscv-target.
		* riscv-target: Directory moved from TestStructure/riscv-target
		* TestStructure/riscv-test-env: Directory moved to riscv-test-env.
		* riscv-test-env: Directory moved from
		TestStructure/riscv-test-env.
		* TestStructure/riscv-test-suite: Directory moved to
		riscv-test-suite.
		* riscv-test-suite: Directory moved from
		TestStructure/riscv-test-suite.
		* thought-experiments: Directory deleted.
	
	2018-05-21  Jeremy Bennett  <jeremy.bennett@embecosm.com>
	
		Initial commit to populate the repository.
	
		* ChangeLog: Created.
		* README.md: Created.
