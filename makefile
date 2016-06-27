.PHONY: clean run

run:	clean AlgoW.hs
	ghc --make -fno-warn-warnings-deprecations ./AlgoW.hs -o AlgoW && ./AlgoW

clean:
	rm -f *.hi *.o AlgoW

