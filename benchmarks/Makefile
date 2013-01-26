EBIN=ebin
ERLC_FLAGS=-pa ebin
SOURCES=$(wildcard *.erl)
HEADERS=$(wildcard *.hrl)
OBJECTS=$(SOURCES:%.erl=$(EBIN)/%.beam)

all: $(OBJECTS) scp noscp hipe_scp hipe_noscp run

$(EBIN)/%.beam: %.erl $(HEADERS) Makefile
	@mkdir -p $(EBIN)
	erlc $(ERLC_FLAGS) -o $(EBIN)/ $<

scp:
	@make -f Makefile.mods EBIN=ebin-scp ERLC_FLAGS="-pa ../ebin -DSUPERCOMPILE"
noscp:
	@make -f Makefile.mods EBIN=ebin-noscp ERLC_FLAGS="-pa ../ebin"
hipe_scp:
	@make -f Makefile.mods EBIN=ebin-hipe_scp ERLC_FLAGS="-pa ../ebin +native -DSUPERCOMPILE"
hipe_noscp:
	@make -f Makefile.mods EBIN=ebin-hipe_noscp ERLC_FLAGS="-pa ../ebin +native"
clean:
	@make -f Makefile.mods clean EBIN=ebin-scp
	@make -f Makefile.mods clean EBIN=ebin-noscp
	@make -f Makefile.mods clean EBIN=ebin-hipe_scp
	@make -f Makefile.mods clean EBIN=ebin-hipe_noscp
	-rm -f $(OBJECTS)

run:
	erl -noshell -pa ebin -pa ebin-noscp -eval 'bench:run(noscp)' -s init stop
	erl -noshell -pa ebin -pa ebin-scp -eval 'bench:run(scp)' -s init stop
	erl -noshell -pa ebin -pa ebin-hipe_noscp -eval 'bench:run(hipe_noscp)' -s init stop
	erl -noshell -pa ebin -pa ebin-hipe_scp -eval 'bench:run(hipe_scp)' -s init stop
