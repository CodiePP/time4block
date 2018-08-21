calculator.js: calculator.hs
	hastec -v --opt-all calculator.hs

clean:
	rm calculator.js *.o *.hi *.jsmod

