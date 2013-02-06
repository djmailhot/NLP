# read in the files
#   one tokenized sentence per line
# determine a vocabulary V
#
# divide each file into 3 data sets
#   training
#   hold-out
#   test
#
# write out data files for train, holdout, test, and vocab



require 'set'

TEST_PERCENT = 10
HELDOUT_PERCENT = 10

LINE_CUTOFF = 5000

# parses vocab tokens from the specified text line
# returns a list of vocab tokens
#
def parse_vocab(line)
  line.split(/[ \t]+/)
end


# reads data from the specified file
# returns a list of lines and a list of vocab tokens
#
def read_file(path)
  lines = []
  count = 0
  vocab = Set.new
  File.open(path, "r:ISO-8859-1").each do |line|
    line = line.strip
    vocab.merge(parse_vocab(line))
    lines << line
    count += 1
  end
  return lines, vocab
end

# writes the data to the specified file
#
def write_file(dir, file, data)
  File.open("#{dir}/#{file}.data", "w") do |file|
    file.write(data.to_a.join("\n"))
  end
end



file_path = ARGV[0]

puts "reading in the file #{file_path}"
lines, vocab = read_file(file_path)


puts "dividing the data"
# determine the division of training, heldout, and test data
data_size = (LINE_CUTOFF || lines.size)
test_size = data_size / TEST_PERCENT
heldout_size = data_size / HELDOUT_PERCENT

test = lines.sample(test_size) 
test_set = test.to_set
lines.reject! { |item| test_set.include?(item) }
data_size -= test_size

heldout = lines.sample(heldout_size)
heldout_set = heldout.to_set
lines.reject! { |item| heldout_set.include?(item) }
data_size -= heldout_size

if lines.size == data_size
  train = lines
else
  train = lines.sample(data_size)
end

puts "writing out the results"
# write results to appropriate data files
file_name = File.split(file_path)[1].split(".")[0]

write_file("train", file_name, train)
write_file("heldout", file_name, heldout)
write_file("test", file_name, test)
write_file("vocab", file_name, vocab)

train = heldout = test = vocab = nil
