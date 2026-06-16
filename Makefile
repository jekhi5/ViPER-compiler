SNAKE_EXT=viper
BUILD=_build
UNAME := $(shell uname)
ifeq ($(UNAME), Linux)
  NASM_FORMAT=elf64
  CLANG_FLAGS=-mstackrealign -m64 -g -fstack-protector-all -Wstack-protector -fno-omit-frame-pointer -z noexecstack -no-pie -gdwarf-4
else
ifeq ($(UNAME), Darwin)
  NASM_FORMAT=macho64
  CLANG_FLAGS=-mstackrealign -m64 -g -fstack-protector-all -Wstack-protector -fno-omit-frame-pointer -arch x86_64
endif
endif

# Location for generated docs to be served.
# The doc sources (.mld files) themselves live in src/doc/.
DOCS_BUILD_DIR=_build/_doc/viper
DOCS_OUTPUT_DIR=docs

PKGS=ounit2,extlib,unix,str
BUILD=ocamlbuild -r -use-ocamlfind -cflag -annot -ocamlyacc 'ocamlyacc -v'

main: src/*.ml src/parser.mly src/lexer.mll
	$(BUILD) -I src -package $(PKGS) main.native
	mv main.native main

.PHONY: doc
doc: doc/*
	./scripts/build-docs.sh -v
	rm -rf $(DOCS_OUTPUT_DIR)
	mkdir $(DOCS_OUTPUT_DIR)
	cp -r $(DOCS_BUILD_DIR)/_html $(DOCS_OUTPUT_DIR)

test: src/*.ml src/parser.mly src/lexer.mll main $(ALL_RUNS)
	$(BUILD) -I src -package $(PKGS) test/test.native
	mv test.native tester

test/output/%.run: test/output/%.o src/main.c src/gc.c
	clang $(CLANG_FLAGS) -o $@ src/gc.c src/main.c $<

test/output/%.o: test/output/%.s
	nasm -f $(NASM_FORMAT) -o $@ $<

.PRECIOUS: test/output/%.s
test/output/%.s: test/input/%.$(SNAKE_EXT) main
	./main $< > $@

test/output/do_pass/%.run: test/output/do_pass/%.o src/main.c src/gc.c
	clang $(CLANG_FLAGS) -o $@ src/gc.c src/main.c $<

test/output/do_pass/%.o: test/output/do_pass/%.s
	nasm -f $(NASM_FORMAT) -o $@ $<

.PRECIOUS: test/output/do_pass/%.s
test/output/do_pass/%.s: test/input/do_pass/%.$(SNAKE_EXT) main
	./main $< > $@


test/output/dont_pass/%.run: test/output/dont_pass/%.o src/main.c src/gc.c
	clang -g $(CLANG_FLAGS) -o $@ src/gc.c src/main.c $<

test/output/dont_pass/%.o: test/output/dont_pass/%.s
	nasm -f $(NASM_FORMAT) -o $@ $<

.PRECIOUS: test/output/dont_pass/%.s
test/output/dont_pass/%.s: test/input/dont_pass/%.$(SNAKE_EXT) main
	./main $< > $@


test/output/do_err/%.run: test/output/do_err/%.o src/main.c src/gc.c
	clang $(CLANG_FLAGS) -o $@ src/gc.c src/main.c $<

test/output/do_err/%.o: test/output/do_err/%.s
	nasm -f $(NASM_FORMAT) -o $@ $<

.PRECIOUS: test/output/do_err/%.s
test/output/do_err/%.s: test/input/do_err/%.$(SNAKE_EXT) main
	./main $< > $@


test/output/dont_err/%.run: test/output/dont_err/%.o src/main.c src/gc.c
	clang -g $(CLANG_FLAGS) -o $@ src/gc.c src/main.c $<

test/output/dont_err/%.o: test/output/dont_err/%.s
	nasm -f $(NASM_FORMAT) -o $@ $<

.PRECIOUS: test/output/dont_err/%.s
test/output/dont_err/%.s: test/input/dont_err/%.$(SNAKE_EXT) main
	./main $< > $@

gctest.o: gctest.c gc.h
	gcc gctest.c -m64 -c -g -o gctest.o

# gc.o: gc.c gc.h
# 	gcc gc.c -m64 -c -g -o gc.o

# cutest-1.5/CuTest.o: cutest-1.5/CuTest.c cutest-1.5/CuTest.h
# 	gcc -m32 cutest-1.5/CuTest.c -c -g -o cutest-1.5/CuTest.o

# gctest: gctest.o gc.c cutest-1.5/CuTest.o cutest-1.5/CuTest.h
# 	gcc -m32 cutest-1.5/AllTests.c cutest-1.5/CuTest.o gctest.o gc.c -o gctest


clean:
	rm -rf test/output/*.o test/output/*.s test/output/*.dSYM test/output/*.run test/*.log test/*.o
	rm -rf test/output/*/*.o test/output/*/*.s test/output/*/*.dSYM test/output/*/*.run
	rm -rf _build/
	rm -f main tester
