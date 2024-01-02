import os

def extract_blueprint(input_file, output_file):
    with open(input_file, 'r') as infile:
        content = infile.read()

        # Extract text between /%% and %%/ delimiters
        between_delimiters = []
        start_delimiter = '/%%'
        end_delimiter = '%%/'
        start_index = content.find(start_delimiter)
        end_index = content.find(end_delimiter, start_index + len(start_delimiter))
        while start_index != -1 and end_index != -1:
            between_delimiters.append(content[start_index + len(start_delimiter):end_index])
            start_index = content.find(start_delimiter, end_index + len(end_delimiter))
            end_index = content.find(end_delimiter, start_index + len(start_delimiter))

        # Extract text following --%%
        after_double_dash = []
        double_dash_delimiter = '--%%'
        double_dash_index = content.find(double_dash_delimiter)
        while double_dash_index != -1:
            line_start = double_dash_index + len(double_dash_delimiter)
            line_end = content.find('\n', line_start)
            after_double_dash.append(content[line_start:line_end])
            double_dash_index = content.find(double_dash_delimiter, line_end)

    # Combine extracted text
    extracted_text = '\n'.join(between_delimiters + after_double_dash)

    # Write to output file in the output directory
    with open(output_file, 'w') as outfile:
        outfile.write(extracted_text)

def process_files(input_dir, output_dir):
    # Ensure output directory exists
    os.makedirs(output_dir, exist_ok=True)

    # Process each .lean file in the input directory
    for filename in os.listdir(input_dir):
        if filename.endswith(".lean"):
            input_path = os.path.join(input_dir, filename)
            output_filename = os.path.splitext(filename)[0] + '.tex'
            output_path = os.path.join(output_dir, output_filename)
            extract_blueprint(input_path, output_path)

# Replace 'input_directory' and 'output_directory' with your actual directory names
process_files(../HasPrimitives, ../blueprint)
