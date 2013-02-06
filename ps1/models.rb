# construct a model
#
# optimize model parameters
#   run training data through model
#   compare performance on hold-out data
#   fiddle hyper-parameters
#   repeat
#


require 'set'


STOP_FLAG = ";;;"
START_FLAG = ":::"


def read_data(type, domain)
  train = []
  File.open("#{type}/#{domain}.data", 'r:ISO-8859-1').each do |line|
    # add the start and stop tokens to each line
    train << "#{START_FLAG} #{START_FLAG} #{line.strip} #{STOP_FLAG}"
  end
  train
end


def read_vocab(domain)
  vocab = Set.new
  File.open("vocab/#{domain}.data", 'r:ISO-8859-1').each { |line| vocab << line.strip }
  vocab << STOP_FLAG
end


# return a counts mapping for unigram, bigram, and trigram occurances of vocab words
def generate_counts(data)
  counts = {}
  data.each do |line|
    unigram = nil
    bigram = nil
    trigram = nil

    # prepend buffering ghost values so we can represent trigrams of the first word
    tokens = line.split(' ')

    # take a sliding window of the entire line, generating grams as we go
    (1..(tokens.size-1)).to_a.each do |i|
      unigram = tokens[i..i]
      bigram = tokens[i-1..i]
      trigram = tokens[i-2..i]

      counts.store(unigram, counts.fetch(unigram, 0) + 1)
      counts.store(bigram, counts.fetch(bigram, 0) + 1)
      counts.store(trigram, counts.fetch(trigram, 0) + 1)
    end
  end
  counts
end



# linear interpolation
#   3 sets:  uni, bi, tri
#
class LinearInterpModel
  attr_accessor :weights
  attr_accessor :word_count

  def initialize(counts)
    @counts = counts

    # sum the number of words for unigram c(w)/c() calculations
    unigrams = @counts.select { |k, v| k.size == 1 }
    @word_count = unigrams.values.reduce(:+)

    # lambda weights for a Linear Interpolation Model.  Must sum to 1
    @weights = {:uni => 0.1,
                :bi => 0.3,
                :tri => 0.6}
  end

  # returns the probability that the given sentence would be generated under
  # this language model
  def pEstimate(sentence)
    probability = 1
    tokens = sentence.split
    (2..(tokens.size-1)).to_a.each do |i|
      probability *= q(tokens[i-2..i])
    end
    probability
  end

  # q trigram estimate function.  Accepts a list of words of size 3.
  # The list should correspond to conditioned variables (w|u,v) such that [u, v, w]
  def q(trigram)
    # multiply by lambda weights
    return @weights[:tri] * qML(trigram) + 
           @weights[:bi] * qML(trigram[1..2]) +
           @weights[:uni] * qML(trigram[2..2])
  end
      
  # q Max Likelihood function.  Accepts a list of words, up to size 3.
  # The list should correspond to conditioned variables (w|u,v) such that [u, v, w]
  def qML(ngram)
    # if the numerator count is zero, return zero
    if not @counts.include?(ngram) then return 0 end

    # extract a denominator ngram based on the size of the numerator ngram
    dgram = nil
    case ngram.size
    when 3
      # get a bigram
      dgram = ngram[0..1]
    when 2
      # get a unigram
      dgram= ngram[0..0]
    end

    if dgram
      # if the denominator count would be zero, return 0
      if not @counts.include?(dgram) then return 0 end
      return @counts.fetch(ngram, 0).to_f / @counts.fetch(dgram, 0).to_f
    else
      # if the denominator count would be zero, return 0
      if @word_count == 0 then return 0 end
      return @counts.fetch(ngram, 0).to_f / @word_count.to_f
    end

    rescue ZeroDivisionError
      0
  end
end





# katz back-off
#   4 sets:  bi A/B, tri A/B, where A is elements with counts > 0 and B is elements with counts = 0
#
class KatzBackoffModel
  attr_accessor :weights
  attr_accessor :word_count

  def initialize(counts, vocab)
    @counts = counts
    @vocab = vocab
    @beta_gram_cache = {}

    # sum the number of words for unigram c(w)/c() calculations
    unigrams = @counts.select { |k, v| k.size == 1 }
    @word_count = unigrams.values.reduce(:+)

    @discount = 0.5 # total discount applied to p1
    @weights = {:p2 => 0.8, # relative mass application to p2
                :p3 => 0.2} # relative mass application to p3
  end

  # returns the probability that the given sentence would be generated under
  # this language model
  def pEstimate(sentence)
    probability = 1
    tokens = sentence.split
    (2..(tokens.size-1)).to_a.each do |i|
      probability *= p(tokens[i-2..i])
    end
    probability
  end


  # p trigram estimate function.  Accepts a list of words of size 3.
  # The list should correspond to conditioned variables (w|u,v) such that [u, v, w]
  def p(trigram)

    bigram = trigram[1..2]
    unigram = trigram[2..2]
    # see which case we fall into for this backoff scheme
    if @counts.include?(trigram)
      # p1 function, trigram exists
      return pML(trigram, @discount)
    else
      ngram = nil
      beta_gram = nil
      alpha = 0
      if @counts.include?(bigram)
        # p2 function, no trigram but bigram exists
        ngram = bigram
        beta_gram = trigram[0..1] # the words used to help generate a beta-set of zero-count trigram
        # alpha mass redistribution
        alpha = @weights[:p2] * (1 - pML(trigram, @discount))
      else
        # p3 function, no trigram or bigram
        ngram = unigram
        beta_gram = trigram[0..0] # the words used to help generate a beta-set of zero-count bigrams
        # alpha mass redistribution
        alpha = @weights[:p3] * (1 - pML(trigram, @discount))
      end

      numerator = pML(ngram)   
      denominator = @beta_gram_cache.fetch(beta_gram, nil) 
      if not denominator
        dgram = nil
        sum = 0
        @vocab.each do |v| # all permutations of vocab words
          dgram = beta_gram + [v]
          # that are zero-count ngrams of (w,w_i-1,w_i-2) or (w,w_i-1)
          if not @counts.include?(dgram)
            # should be part of the sum of pML(w|w_i-1) or pML(w)
            sum += pML(dgram.drop(1)) # drop w_i-2 or w_i-1 as needed
          end
        end

        @beta_gram_cache.store(beta_gram, sum)
        denominator = sum
      end

      if denominator == 0 then return 0 end
      return alpha * numerator / denominator
    end

  end

  # p Max Likelihood function.  Accepts a list of words, up to size 3.
  # The list should correspond to conditioned variables (w|u,v) such that [u, v, w]
  def pML(ngram, discount=0)
    # if the numerator count is zero, return zero
    if not @counts.include?(ngram) then return 0 end

    # extract a denominator ngram based on the size of the numerator ngram
    dgram = nil
    case ngram.size
    when 3
      dgram = ngram[0..1]
    when 2
      dgram= ngram[0..0]
    end

    result = 0
    if dgram
      # if the denominator count would be zero, return 0
      if not @counts.include?(dgram) then return 0 end
      # discount the numerator if needed
      result = (@counts.fetch(ngram, 0).to_f - discount) / @counts.fetch(dgram, 0).to_f
    else
      if @word_count == 0 then return 0 end
      # discount the numerator if needed
      result = (@counts.fetch(ngram, 0).to_f - discount) / @word_count.to_f
    end

# puts "#{ngram.inspect} #{result}"
    return result

    rescue ZeroDivisionError
      0
  end
end




def perplexity(model, sentences)
  sum = 0
  sentences.each do |s|
    prob = model.pEstimate(s)
    sum += ((prob != 0) ? Math.log( prob ) : Math.log( Float::MIN) )
  end
  l = sum / model.word_count.to_f
  2 ** (-l)
end



domain = ARGV[0]

puts "domain #{domain} selected"

puts "reading in training data"
train = read_data("train", domain)

puts "generating counts for ngrams in training data"
train_counts = generate_counts(train)
train = nil

puts "reading in heldout data"
heldout = read_data("heldout", domain)


#puts "generating counts for ngrams in heldout data"
#heldout_counts = generate_counts(heldout)

li_model = LinearInterpModel.new(train_counts)
puts "linear interpolation perplexity"
puts perplexity(li_model, heldout)
li_model = nil




puts "reading in vocab"
vocab = read_vocab(domain)

kb_model = KatzBackoffModel.new(train_counts, vocab)
puts "katz backoff perplexity"
puts perplexity(kb_model, heldout)


