interpreter: syntax src/*.hs
	cd src && ghc -outputdir build Main.hs -o ../interpreter

syntax: clean syntax.cf
	bnfc -d -m syntax.cf -o syntax
	cd syntax && make
	mv -f syntax/Syntax src/Syntax
	rm -rf syntax

clean:
	rm -rf src/Syntax
	rm -f interpreter
	rm -rf src/build