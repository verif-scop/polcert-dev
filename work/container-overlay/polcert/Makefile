#######################################################################
#                                                                     #
#              The Compcert verified compiler                         #
#                                                                     #
#          Xavier Leroy, INRIA Paris-Rocquencourt                     #
#                                                                     #
#  Copyright Institut National de Recherche en Informatique et en     #
#  Automatique.  All rights reserved.  This file is distributed       #
#  under the terms of the GNU Lesser General Public License as        #
#  published by the Free Software Foundation, either version 2.1 of   #
#  the License, or (at your option) any later version.                #
#  This file is also distributed under the terms of the               #
#  INRIA Non-Commercial License Agreement.                            #
#                                                                     #
#######################################################################

include Makefile.config
include VERSION

BUILDVERSION ?= $(version)
BUILDNR ?= $(buildnr)
TAG ?= $(tag)
BRANCH ?= $(branch)

ifeq ($(wildcard $(ARCH)_$(BITSIZE)),)
ARCHDIRS=$(ARCH)
else
ARCHDIRS=$(ARCH)_$(BITSIZE) $(ARCH)
endif

DIRS := lib common $(ARCHDIRS) cfrontend driver cparser src polygen samples syntax

COQINCLUDES := $(foreach d, $(DIRS), -R $(d) polcert.$(d))

ifeq ($(LIBRARY_FLOCQ),local)
DIRS += flocq/Core flocq/Prop flocq/Calc flocq/IEEE754
COQINCLUDES += -R flocq Flocq
endif

ifeq ($(LIBRARY_MENHIRLIB),local)
DIRS += MenhirLib
COQINCLUDES += -R MenhirLib MenhirLib
endif

ifeq ($(LIBRARY_VPL),local)
DIRS += VPL/coq
COQINCLUDES += -R VPL/coq Vpl
endif

# Notes on silenced Coq warnings:
#
# unused-pattern-matching-variable:
#    warning introduced in 8.13
#    the code rewrite that avoids the warning is not desirable
# deprecated-ident-entry:
#    warning introduced in 8.13
#    suggested change (use `name` instead of `ident`) supported since 8.13
# implicit-core-hint-db: inherit from PolyGen, to be solved upsteam
# deprecated-hint-without-locality: inherit from PolyGen, to be solved upsteam
# undeclared-scope: library file, to be solved
COQCOPTS ?= \
  -w -unused-pattern-matching-variable \
  -w -deprecated-ident-entry \
  -w -implicit-core-hint-db \
  -w -deprecated-hint-without-locality \
  -w -undeclared-scope

# deprecated-instance-without-locality:
#    warning introduced in 8.14
#    triggered by Menhir-generated files, to be solved upstream in Menhir
# cparser/Parser.vo: COQCOPTS += -w -deprecated-instance-without-locality

COQC="$(COQBIN)coqc" -q $(COQINCLUDES) $(COQCOPTS)
COQDEP="$(COQBIN)coqdep" $(COQINCLUDES)
COQDOC="$(COQBIN)coqdoc"
COQEXEC="$(COQBIN)coqtop" $(COQINCLUDES) -batch -load-vernac-source
COQCHK="$(COQBIN)coqchk" $(COQINCLUDES)
MENHIR=menhir
CP=cp

VPATH=$(DIRS)
GPATH=$(DIRS)

# Flocq

ifeq ($(LIBRARY_FLOCQ),local)
FLOCQ=\
  Raux.v Zaux.v Defs.v Digits.v Float_prop.v FIX.v FLT.v FLX.v FTZ.v \
  Generic_fmt.v Round_pred.v Round_NE.v Ulp.v Core.v \
  Bracket.v Div.v Operations.v Plus.v Round.v Sqrt.v \
  Div_sqrt_error.v Mult_error.v Plus_error.v \
  Relative.v Sterbenz.v Round_odd.v Double_rounding.v \
  BinarySingleNaN.v Binary.v Bits.v
else
FLOCQ=
endif

# General-purpose libraries (in lib/)

VLIB=Axioms.v BoolEqual.v Coqlib.v Intv.v Maps.v \
  Zbits.v Integers.v Archi.v IEEE754_extra.v Floats.v \
  Decidableplus.v Misc.v ImpureOperations.v ImpureAlarmConfig.v \
  LibTactics.v Linalg.v LinalgExt.v Mymap.v sflib.v \
  TopoSort.v VplInterface.v Heuristics.v Ordered.v ListExt.v

# Parts common to the front-ends and the back-end (in common/)

COMMON=Errors.v AST.v Linking.v \
  Events.v Globalenvs.v Memdata.v Memtype.v Memory.v \
  Values.v Smallstep.v Separation.v Builtins0.v Builtins1.v Builtins.v

# C front-end modules (in cfrontend/)

CFRONTEND=Ctypes.v Cop.v Csyntax.v Csem.v Ctyping.v Cstrategy.v Initializers.v Initializersproof.v

# TODO: May remove some files

BACKEND=
# Machregs.v Conventions1.v Locations.v Op.v

POLYGEN=ASTGen.v Canonizer.v CodeGen.v TyTy.v StateTy.v InstrTy.v Loop.v LoopGen.v \
  ParallelLoop.v \
  PolyLang.v PolyLoop.v PolyLoopSimpl.v PolyOperations.v PolyTest.v \
  Projection.v Result.v IterSemantics.v PolIRs.v CPolIRs.v TPolIRs.v InstanceListSema.v \
  LoopCleanup.v LoopSingletonCleanup.v

# Parser

PARSER=Cabs.v Parser.v

# MenhirLib

ifeq ($(LIBRARY_MENHIRLIB),local)
MENHIRLIB=Alphabet.v Automaton.v Grammar.v Interpreter_complete.v \
  Interpreter_correct.v Interpreter.v Main.v Validator_complete.v \
  Validator_safe.v Validator_classes.v
else
MENHIRLIB=
endif

# VPL (Verified Polyhedra Library)
ifeq ($(LIBRARY_VPL),local)
VPLLIB=ASAtomicCond.v ASCond.v AssignD.v ASTerm.v CIndex.v ConsSet.v \
  CoqAddOn.v CstrC.v CstrLCF.v Debugging.v DemoPLTests.v \
  DemoPLVerifier.v DomainFunctors.v DomainGCL.v DomainInterfaces.v \
  DomainGCL.v Impure.v ImpureConfig.v Itv.v LinearizeBackend.v LinTerm.v \
  Map_poly.v NumC.v OptionMonad.v PedraQ.v PedraQBackend.v PedraZ.v \
  PositiveMapAddOn.v PredTrans.v ProgVar.v Qop.v Ring_polynom_AddOn.v \
  Ring_polynom_AddOnQ.v ZNone.v ZNoneItv.v  
else
VPLLIB=
endif

# Source of PolCert

POLCERT_SRC = Base.v Convert.v \
  Extractor.v PrepareCodegen.v StrengthenDomain.v \
  OpenScop.v OpenScopAST.v PolyBase.v PolyLang.v \
  SelectionSort.v StablePermut.v CState.v AffineValidator.v \
  ParallelValidator.v ParallelCodegen.v \
  PointWitness.v ISSWitness.v ISSRefinement.v \
  ISSBoolChecker.v ISSValidator.v ISSSemantics.v \
  ISSCutSemantics.v ISSValidatorCorrect.v \
  TilingWitness.v TilingList.v TilingRelation.v \
  TilingBoolChecker.v TilingValidator.v TilingBandScheduleValidator.v \
  TilingCanonicalScheduleValidator.v Validator.v \
  CInstr.v TInstr.v CTy.v

# Putting everything together (in driver/)

DRIVER=PolOpt.v PolOptCanonicalTiling.v PolOptBandTiling.v ParallelPolOpt.v ParallelPolOptCorrect.v PolOptCorrect.v PolOptPrepared.v CPolOpt.v TPolOpt.v TPolValidator.v

SAMPLES=CSample1.v CSample2.v CSample3.v ExtractorSmoke.v

SYNTAX_EXPERIMENT=SInstr.v SPolIRs.v SPolOpt.v SParallelPolOpt.v STilingOpt.v STilingBandSched.v SBandTilingOpt.v SInstrSmoke.v

# Library for .v files generated by clightgen

# ifeq ($(CLIGHTGEN),true)
# EXPORTLIB=Ctypesdefs.v Clightdefs.v Csyntaxdefs.v
# else
# EXPORTLIB=
# endif

# All source files

FILES=$(VPLLIB) $(VLIB) $(COMMON) $(CFRONTEND) $(DRIVER) $(FLOCQ) \
  $(MENHIRLIB) $(POLYGEN) $(POLCERT_SRC) $(DRIVER) $(SAMPLES) \
  $(SYNTAX_EXPERIMENT)

# $(PARSER) $(BACKEND)
# Generated source files

# GENERATED = cparser/Parser.v VPL/ocaml/src/Wrapper.ml
GENERATED = VPL/ocaml/src/Wrapper.ml


all:
	@test -f .depend || $(MAKE) depend
	$(MAKE) proof
	$(MAKE) extraction
	$(MAKE) polcert
	$(MAKE) polopt

# $(MAKE) polcert # we don't compile the full polyhedral compiler now 

proof: $(FILES:.v=.vo)

# Turn off some warnings for Flocq and Menhirlib (& VPL)
# These warnings can only be addressed upstream

flocq/%.vo: COQCOPTS+=-w -deprecated-syntactic-definition
MenhirLib/%.vo: COQCOPTS+=-w -deprecated-syntactic-definition
VPL/%.vo: COQCOPTS+=-w -deprecated-syntactic-definition -w -deprecated-cutrewrite -w -fragile-hint-constr -w -implicit-core-hint-db -w -deprecated-hint-without-locality -w -deprecated-grab-existentials -w -notation-overridden -w -undeclared-scope -w -require-in-module -w -unused-intro-pattern -w -deprecated-focus -w -extraction-opaque-accessed

extraction: extraction/STAMP

extraction/STAMP: $(FILES:.v=.vo) extraction/extraction.v $(ARCH)/extractionMachdep.v
	rm -f extraction/*.ml extraction/*.mli
	$(COQEXEC) extraction/extraction.v
	@if grep 'AXIOM TO BE REALIZED' extraction/*.ml; then \
            echo "An error occured during extraction to OCaml code."; \
            echo "Check the versions of Flocq and MenhirLib used."; \
            exit 2; \
         fi
	rm -f extraction/ImpureConfig.mli extraction/SParallelPolOpt.mli
	touch extraction/STAMP

.depend.extr: extraction/STAMP tools/modorder driver/Version.ml
	$(MAKE) -f Makefile.extr depend

polcert: .depend.extr polcert.ini driver/Version.ml FORCE
	$(MAKE) -f Makefile.extr polcert

polopt: .depend.extr driver/Version.ml FORCE
	$(MAKE) -f Makefile.extr polopt

GENERATED_SLOW_CASES=adi dct dsyr2k fdtd-1d fdtd-2d jacobi-1d-imper jacobi-2d-imper lu matmul-seq matmul-seq3 mxv-seq mxv-seq3 polynomial tce

FORCE:

.PHONY: proof extraction FORCE test test-polopt-loop-suite test-polopt-generated test-iss-pluto-suite test-end-to-end-c-smoke test-end-to-end-c-perf test-end-to-end-generated-smoke test-end-to-end-generated-perf-default test-end-to-end-generated-perf test-end-to-end-generated-heavy test-end-to-end-generated test-end-to-end-generated-perf-parallel test-end-to-end-generated-slow-perf-parallel search-end-to-end-generated-best report-end-to-end-generated-best test-end-to-end-generated-perf-refresh tune-end-to-end-generated test-end-to-end-all test-pluto-bug-matmul-parallel-hint profile-advect3d-codegen profile-advect3d-codegen-identity

test: .depend.extr polcert.ini driver/Version.ml FORCE
	$(MAKE) -f Makefile.test test --no-print-directory

test-polopt-loop-suite: polopt
	rm -rf tests/polopt-generated/cases
	python3 tests/polopt-generated/tools/materialize_polopt_cases.py \
		--polopt ./polopt \
		--timeout-seconds 300

test-polopt-generated: test-polopt-loop-suite
	python3 tests/polopt-generated/tools/check_polopt_cases.py \
		--cases-dir tests/polopt-generated/cases \
		--expect-total 62 \
		--min-changed 50 \
		--min-nontrivial-changed 50 \
		--require-tiled matmul matmul-init wavefront

test-iss-pluto-suite: polopt polcert.ini
	./polopt --validate-iss-pluto-suite

test-iss-pluto-live-suite: polopt polcert.ini
	./polopt --validate-iss-pluto-live-suite

test-end-to-end-c-smoke: polopt
	python3 tools/end_to_end_c/run_suite.py \
		--polopt ./polopt \
		matmul reverse_iss

test-end-to-end-c-perf: polopt
	python3 tools/end_to_end_c/run_suite.py \
		--polopt ./polopt \
		--output-root tests/end-to-end-c/out-perf \
		--benchmark-repeats 3 \
		matmul_perf reverse_iss_perf

test-end-to-end-generated-smoke: test-polopt-loop-suite
	python3 tools/end_to_end_c/run_generated_suite.py \
		--cases-root tests/polopt-generated/cases \
		--output-root tests/end-to-end-generated/out \
		--tier smoke \
		--benchmark-repeats 1

test-end-to-end-generated-perf-default: test-polopt-loop-suite
	python3 tools/end_to_end_c/run_generated_suite.py \
		--cases-root tests/polopt-generated/cases \
		--output-root tests/end-to-end-generated/out-perf \
		--tier perf \
		--benchmark-repeats 1

test-end-to-end-generated-perf: test-polopt-loop-suite
	python3 tools/end_to_end_c/run_generated_suite.py \
		--cases-root tests/polopt-generated/cases \
		--polopt ./polopt \
		--pipeline-config tests/end-to-end-generated/best_pipelines.json \
		--output-root tests/end-to-end-generated/out-perf-best \
		--tier perf \
		--benchmark-repeats 1

test-end-to-end-generated-heavy: test-polopt-loop-suite
	python3 tools/end_to_end_c/run_generated_suite.py \
		--cases-root tests/polopt-generated/cases \
		--output-root tests/end-to-end-generated/out-heavy \
		--tier heavy \
		--benchmark-repeats 1

test-end-to-end-generated-perf-parallel: test-polopt-loop-suite
	python3 tools/end_to_end_c/run_generated_suite.py \
		--cases-root tests/polopt-generated/cases \
		--polopt ./polopt \
		--polopt-arg --parallel \
		--output-root tests/end-to-end-generated/out-perf-parallel \
		--tier perf \
		--omp-threads 4 \
		--benchmark-repeats 1

test-end-to-end-generated-slow-perf-parallel: test-polopt-loop-suite
	python3 tools/end_to_end_c/run_generated_suite.py \
		--cases-root tests/polopt-generated/cases \
		--polopt ./polopt \
		--polopt-arg --parallel \
		--output-root tests/end-to-end-generated/out-perf-parallel-slow \
		--tier perf \
		--omp-threads 4 \
		--benchmark-repeats 1 \
		$(GENERATED_SLOW_CASES)

search-end-to-end-generated-best: test-polopt-loop-suite
	python3 tools/end_to_end_c/search_best_generated_pipelines.py \
		--cases-root tests/polopt-generated/cases \
		--polopt ./polopt \
		--pipeline-config tests/end-to-end-generated/pipeline_candidates.json \
		--output-root tests/end-to-end-generated/search \
		--summary-out tests/end-to-end-generated/best_pipelines.json \
		--report-out tests/end-to-end-generated/best_pipeline_report.json \
		--tier perf \
		--benchmark-repeats 1

report-end-to-end-generated-best:
	python3 tools/end_to_end_c/generate_best_pipeline_table.py \
		--summary-in tests/end-to-end-generated/best_pipelines.json \
		--report-in tests/end-to-end-generated/best_pipeline_report.json \
		--output tests/end-to-end-generated/BEST_PIPELINES.md

test-end-to-end-generated-perf-refresh: search-end-to-end-generated-best report-end-to-end-generated-best test-end-to-end-generated-perf

test-end-to-end-generated: test-end-to-end-generated-perf

tune-end-to-end-generated:
	python3 tools/end_to_end_c/tune_generated_params.py \
		--cases-root tests/polopt-generated/cases \
		--param-config tests/end-to-end-generated/param_tiers.json \
		--target-seconds 1.0 \
		--max-seconds 12.0 \
		--trial-timeout-seconds 8.0

test-end-to-end-all: test-end-to-end-c-smoke test-end-to-end-c-perf test-end-to-end-generated-perf

test-pluto-bug-matmul-parallel-hint: polopt polcert.ini
	python3 tools/pluto_bugs/run_matmul_parallel_hint.py

profile-advect3d-codegen: polopt
	python3 tools/perf/run_stage_profile.py \
		--polopt ./polopt \
		--mode affine \
		tests/polopt-generated/inputs/advect3d.loop

profile-advect3d-codegen-identity: polopt
	python3 tools/perf/run_stage_profile.py \
		--polopt ./polopt \
		--mode identity \
		tests/polopt-generated/inputs/advect3d.loop

test-clean: 
	$(MAKE) -f Makefile.test clean

documentation: $(FILES)
	mkdir -p doc/html
	rm -f doc/html/*.html
	./tools/coq2html -d doc/html/ -base polcert -short-names doc/*.glob \
          $(filter-out doc/coq2html cparser/Parser.v, $^)
	cp -r doc/html/ /var/www/html

tools/ndfun: tools/ndfun.ml
ifeq ($(OCAML_NATIVE_COMP),true)
	ocamlopt -o tools/ndfun str.cmxa tools/ndfun.ml
else
	ocamlc -o tools/ndfun str.cma tools/ndfun.ml
endif

tools/modorder: tools/modorder.ml
ifeq ($(OCAML_NATIVE_COMP),true)
	ocamlopt -o tools/modorder str.cmxa tools/modorder.ml
else
	ocamlc -o tools/modorder str.cma tools/modorder.ml
endif


%.vo: %.v
	@rm -f doc/$(*F).glob
	@echo "COQC $<"
	@$(COQC) -dump-glob doc/$(*F).glob $<

%.v: %.vp tools/ndfun
	@rm -f $*.v
	@echo "Preprocessing $*.vp"
	@tools/ndfun $*.vp > $*.v || { rm -f $*.v; exit 2; }
	@chmod a-w $*.v

polcert.ini: Makefile.config
	(echo "stdlib_path=$(LIBDIR)"; \
         echo "prepro=$(CPREPRO)"; \
         echo "linker=$(CLINKER)"; \
         echo "asm=$(CASM)"; \
	 echo "prepro_options=$(CPREPRO_OPTIONS)";\
	 echo "asm_options=$(CASM_OPTIONS)";\
	 echo "linker_options=$(CLINKER_OPTIONS)";\
         echo "arch=$(ARCH)"; \
         echo "model=$(MODEL)"; \
         echo "abi=$(ABI)"; \
         echo "endianness=$(ENDIANNESS)"; \
         echo "system=$(SYSTEM)"; \
         echo "has_runtime_lib=$(HAS_RUNTIME_LIB)"; \
         echo "has_standard_headers=$(HAS_STANDARD_HEADERS)"; \
         echo "asm_supports_cfi=$(ASM_SUPPORTS_CFI)"; \
	 echo "response_file_style=$(RESPONSEFILE)";) \
        > polcert.ini
# echo "scheduler=$(PLUTO)"; \
# echo "scheduler_options=$(PLUTO_OPTIONS);



# polcert.config: Makefile.config
# 	(echo "# CompCert configuration parameters"; \
#         echo "COMPCERT_ARCH=$(ARCH)"; \
#         echo "COMPCERT_MODEL=$(MODEL)"; \
#         echo "COMPCERT_ABI=$(ABI)"; \
#         echo "COMPCERT_ENDIANNESS=$(ENDIANNESS)"; \
#         echo "COMPCERT_BITSIZE=$(BITSIZE)"; \
#         echo "COMPCERT_SYSTEM=$(SYSTEM)"; \
#         echo "COMPCERT_VERSION=$(BUILDVERSION)"; \
#         echo "COMPCERT_BUILDNR=$(BUILDNR)"; \
#         echo "COMPCERT_TAG=$(TAG)"; \
#         echo "COMPCERT_BRANCH=$(BRANCH)" \
#         ) > compcert.config

driver/Version.ml: VERSION
	(echo 'let version = "$(BUILDVERSION)"'; \
         echo 'let buildnr = "$(BUILDNR)"'; \
         echo 'let tag = "$(TAG)"'; \
         echo 'let branch = "$(BRANCH)"') > driver/Version.ml

# cparser/Parser.v: cparser/Parser.vy
# 	@rm -f $@
# 	$(MENHIR) --coq --coq-no-version-check cparser/Parser.vy
# 	@chmod a-w $@

VPL/ocaml/src/Wrapper.ml: 
	cp -f VPL/ocaml/src/Wrapper_no_glpk.ml VPL/ocaml/src/Wrapper.ml

depend: $(GENERATED) depend1

depend1: $(FILES)
	@echo "Analyzing Coq dependencies"
	@$(COQDEP) $^ > .depend

install:
	install -d $(DESTDIR)$(BINDIR)
	install -m 0755 ./polcert $(DESTDIR)$(BINDIR)
	install -d $(DESTDIR)$(SHAREDIR)
	install -m 0644 ./polcert.ini $(DESTDIR)$(SHAREDIR)

clean:
	rm -f $(patsubst %, %/*.vo*, $(DIRS))
	rm -f $(patsubst %, %/.*.aux, $(DIRS))
	rm -rf doc/html doc/*.glob
	rm -f driver/Version.ml
	rm -f polcert.ini
	rm -f extraction/STAMP extraction/*.ml extraction/*.mli .depend.extr
	rm -f tools/ndfun tools/modorder tools/*.cm? tools/*.o
	rm -f $(GENERATED) .depend
	rm -f .lia.cache
	rm -f result.txt
	$(MAKE) -f Makefile.extr clean
	$(MAKE) -f Makefile.test clean


camlclean:
	rm -f extraction/STAMP extraction/*.ml extraction/*.mli 
	rm -f VPL/ocaml/src/extracted/*.ml VPL/ocaml/src/extracted/*.mli 
	rm -f .depend.extr 
	rm -f $(GENERATED) .depend
	$(MAKE) -f Makefile.extr clean


distclean:
	$(MAKE) clean
	rm -f Makefile.config

check-admitted: $(FILES)
	@grep -w 'admit\|Admitted\|ADMITTED' $^ || echo "Nothing admitted."

print-includes:
	@echo $(COQINCLUDES)

loc:
	cloc src --include-lang=Coq --force-lang=Coq,.v --by-file-by-lang

CoqProject:
	@echo $(COQINCLUDES) > _CoqProject

-include .depend

FORCE:
