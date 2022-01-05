all: compiler

coq: Browser BrowserStates BrowserLemmas

%: model/%.v
	cd model && dune exec -- coqc $(notdir $<)

compiler:
	cd compiler && dune build

clean:
	cd compiler && dune clean
	cd model && dune clean
	find ./model -type f -name "*.vos" -delete
	find ./model -type f -name "*.vok" -delete
	find ./model -type f -name "*.vo" -delete
	find ./model -type f -name "*.glob" -delete
	find ./model -type f -name "*.aux" -delete
	find ./model -type f -name ".lia.cache" -delete

.PHONY: all compiler coq wrapper
