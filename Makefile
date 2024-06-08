REQUIRED_DIRS := build

graph.pdf: build/Program.class BinarySearch.class
	java -cp build Program BinarySearch.class

BinarySearch.class: binsearch.java
	javac binsearch.java

build/Program.class: src/Program.java
	javac src/Program.java -d build

$(shell mkdir -p $(REQUIRED_DIRS))
