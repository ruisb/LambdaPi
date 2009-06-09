lp:
	ghc --make -o lp MainLP.hs

st:
	ghc --make -o st MainST.hs

original:
	ghc --make -o original OriginalCode/OriginalLambdaPi.hs

clean:
	rm */*.o
	rm */*.hi
	rm *.o
	rm *.hi
	rm lp
	rm st
