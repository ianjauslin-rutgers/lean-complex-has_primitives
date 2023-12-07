build:
	lake update
	lake exe cache get
	lake build

doc: clean-doc
	lake -R -Kenv=dev build HasPrimitives:docs
clean-doc:
	rm -rf .lake/build/doc/*

blueprint: clean-blueprint
	make -C blueprint
	make -C blueprint clean-aux
clean-blueprint:
	make -C blueprint clean

clean: clean-doc clean-blueprint
