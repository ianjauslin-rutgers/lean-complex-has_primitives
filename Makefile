LAKEBIN=lake

build:
	$(LAKEBIN) update
	$(LAKEBIN) exe cache get
	$(LAKEBIN) build

doc: clean-doc .lake/packages/doc-gen4
	$(LAKEBIN) -R -Kenv=dev build HasPrimitives:docs
.lake/packages/doc-gen4:
	$(LAKEBIN) -R -Kenv=dev update
clean-doc:
	rm -rf .lake/build/doc/*

blueprint: clean-blueprint
	make -C blueprint
	make -C blueprint clean-aux
clean-blueprint:
	make -C blueprint clean

clean: clean-doc clean-blueprint
