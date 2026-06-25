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

PREFIX     ?= $(HOME)/.local
BINDIR     = $(PREFIX)/bin
LIBDIR     = $(PREFIX)/lib/viper

# Location for generated docs to be served.
# The doc sources (.mld files) themselves live in src/doc/.
DOCS_BUILD_DIR=_build/_doc/viper
DOCS_OUTPUT_DIR=docs

# Location of the C runtime files.
# For dev, set this to src.
# For release, set this to the lib dir.
RUNTIME_DIR=$(CURDIR)/src

PKGS=ounit2,extlib,unix,str
BUILD=ocamlbuild -r -use-ocamlfind -cflag -annot -ocamlyacc 'ocamlyacc -v'

main: src/*.ml src/parser.mly src/lexer.mll executable/config.ml
	-dune fmt
	$(BUILD) -I src -package $(PKGS) main.native executable/viperc.native
	mv main.native main
	mv viperc.native viperc

executable/config.ml: Makefile
	@echo "(* Auto-generated — do not edit *)"   > $@
	@echo "let nasm_format = \"$(NASM_FORMAT)\"" >> $@
	@echo "let clang_flags = \"$(CLANG_FLAGS)\"" >> $@
	@echo "let runtime_dir = \"$(RUNTIME_DIR)\"" >> $@

viperc: executable/config.ml
	$(BUILD) -I executable executable/viperc.native
	mv viperc.native viperc

.PHONY: install uninstall doc

install:
	install -d $(BINDIR)
	install -d $(LIBDIR)
	install -m 755 viperc $(BINDIR)/viperc
	install -m 644 src/main.c $(LIBDIR)/main.c
	install -m 644 src/gc.c $(LIBDIR)/gc.c
	install -m 644 src/gc.h $(LIBDIR)/gc.h

uninstall:
	rm -f $(BINDIR)/viperc
	rm -f $(LIBDIR)/main.c
	rm -f $(LIBDIR)/gc.c
	rm -f $(LIBDIR)/gc.h
	-rmdir  $(LIBDIR)

doc: doc/*
	./scripts/build-docs.sh -v
	rm -rf $(DOCS_OUTPUT_DIR)
	mkdir $(DOCS_OUTPUT_DIR)
	cp -r $(DOCS_BUILD_DIR)/_html $(DOCS_OUTPUT_DIR)

test: src/*.ml src/parser.mly src/lexer.mll main
	mkdir -p test/output/do_err test/output/do_pass test/output/dont_err test/output/dont_pass
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
	rm -f main tester viperc viper
	rm -f executable/config.ml
