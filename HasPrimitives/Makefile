INPUT_DIR := ../HasPrimitives
OUTPUT_DIR := ../blueprint

extract_blueprint: $(patsubst $(INPUT_DIR)/%.lean,$(OUTPUT_DIR)/%.tex,$(wildcard $(INPUT_DIR)/*.lean))

$(OUTPUT_DIR)/%.tex: $(INPUT_DIR)/%.lean
	python3 extract_blueprint.py

.PHONY: extract_blueprint
