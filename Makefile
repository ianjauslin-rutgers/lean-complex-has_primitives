LAKEBIN=lake

build:
	$(LAKEBIN) update
	$(LAKEBIN) exe cache get
	$(LAKEBIN) build

doc: clean-doc
	$(LAKEBIN) -R -Kenv=dev build HasPrimitives:docs
clean-doc:
	rm -rf .lake/build/doc/*

blueprint: clean-blueprint
	make -C blueprint
	make -C blueprint clean-aux
clean-blueprint:
	make -C blueprint clean

clean: clean-doc clean-blueprint
