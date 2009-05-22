all:
	ghc --make -o lp Main.hs

clean:
	rm */*.o
	rm */*.hi
	rm *.o
	rm *.hi
	rm lp