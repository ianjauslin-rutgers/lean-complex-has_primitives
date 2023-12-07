doc: clean-doc
	lake -R -Kenv=dev build HasPrimitives:docs
clean-doc:
	rm -rf .lake/build/doc/*
doc-upload:
	rsync -rha --progress --delete .lake/build/doc webmaster@jauslin.org:jauslin.org/lean-complex-has_primitives-doc/doc

blueprint: clean-blueprint
	make -C blueprint
	make -C blueprint clean-aux
clean-blueprint:
	make -C blueprint clean
blueprint-upload:
	rsync -rha --progress --delete blueprint/web webmaster@jauslin.org:jauslin.org/lean-complex-has_primitives-doc/blueprint

upload: doc-upload blueprint-upload

clean: clean-doc clean-blueprint
