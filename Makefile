LAKEBIN=lake

PROJECT=HasPrimitives

FILES=$(basename $(notdir $(wildcard $(PROJECT)/*.lean)))
BLUEPRINTS=$(addsuffix .tex, $(addprefix blueprint/, $(FILES)))
BLUEPRINT_FILE=blueprint/blueprint.tex

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

blueprint: $(BLUEPRINTS)

$(BLUEPRINTS):
	python3 leanblueprint-extract/extract_blueprint $(addprefix HasPrimitives/, $(notdir $(addsuffix .lean, $(basename $@)))) > $@

## this can be used to automatically generate blueprint.tex - maybe not the best idea
#$(BLUEPRINT_FILE):
#	cat blueprint/blueprint_template.tex > $@
#	for ff in $(FILES); do
#	  echo "\\input{$$ff.tex}" >> $@
#	done

blueprint: clean-blueprint $(BLUEPRINTS)# $(BLUEPRINT_FILE)
	make -C blueprint
	make -C blueprint clean-aux
clean-blueprint:
	rm -f $(BLUEPRINTS)
	make -C blueprint clean

clean: clean-doc clean-blueprint
