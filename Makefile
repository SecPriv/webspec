.PHONY: all compiler coq wrapper verifier
SHELL=/usr/bin/env bash

all: compiler

coq: compiler Browser BrowserStates BrowserLemmas

%: model/%.v
	cd model && dune exec -- coqc $(notdir $<)

compiler:
	cd compiler && dune build

wrapper:
	cd wrapper && make

verifier/model/Browser.ml: coq OCamlExtract

verifier: verifier/model/Browser.ml
	cd verifier && dune build

clean-verifier-output:
	cd verifier && rm -fr output


define DUNE_FILE
(executable
  (name Z3_Trace)
  (modes (byte exe)))

(env
  (dev
    (flags (:standard -w -33))))
endef

define MARSHAL_PROGRAM

type t = {
  events : Browser.coq_Event list;
  states : Browser.coq_State list;
  global : Browser.coq_Global
}

let () =
  let channel = open_out_bin "./trace.dat" in
  Fun.protect ~finally:(fun () -> close_out channel)
    (fun () ->
      Marshal.to_channel channel ({ events=events; states=states; global=global }) [Marshal.No_sharing])
endef
export DUNE_FILE
export MARSHAL_PROGRAM

traces/%.trace.dat: traces/%.trace.z3
	scripts/z32coq.el $< > model/Z3_Trace.v && \
	TMP=$$(grep -Po 'Cd "\K[^"]+' model/Z3_Trace.v) && \
	pushd model && dune exec coqc Z3_Trace.v && rm Z3_Trace.{v,glob} && popd && \
	echo "$$DUNE_FILE" > $$TMP/dune && \
	echo "$$MARSHAL_PROGRAM" >> $$TMP/Z3_Trace.ml && \
	pushd $$TMP && dune exec ./Z3_Trace.exe && popd && \
	cp $$TMP/trace.dat $@ && rm -fr $$TMP

clean:
	cd compiler && dune clean
	cd model && dune clean
	find ./model -type f -name "*.vos" -delete
	find ./model -type f -name "*.vok" -delete
	find ./model -type f -name "*.vo" -delete
	find ./model -type f -name "*.glob" -delete
	cd wrapper && make clean
	cd verifier && dune clean
	find ./verifier/model -type f -name "*.vo*" -delete
	find ./verifier/model -type f -name "*.glob" -delete
	find ./verifier/model -type f -name "*.ml*" -delete
	find ./traces -type f -name "*.trace.dat" -delete

