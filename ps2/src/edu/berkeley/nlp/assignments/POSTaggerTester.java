package edu.berkeley.nlp.assignments;

import edu.berkeley.nlp.io.PennTreebankReader;
import edu.berkeley.nlp.ling.Tree;
import edu.berkeley.nlp.ling.Trees;
import edu.berkeley.nlp.util.*;

import java.util.*;
import java.util.PriorityQueue;

/**
 * @author Dan Klein
 */
public class POSTaggerTester {

  static final String UNKNOWN_WORD = "<UNK>";
  static final String START_WORD = "<S>";
  static final String STOP_WORD = "</S>";
  static final String START_TAG = "<S>";
  static final String STOP_TAG = "</S>";

  /**
   * Tagged sentences are a bundling of a list of words and a list of their
   * tags.
   */
  static class TaggedSentence {
    List<String> words;
    List<String> tags;

    public int size() {
      return words.size();
    }

    public List<String> getWords() {
      return words;
    }

    public List<String> getTags() {
      return tags;
    }

    public String toString() {
      StringBuilder sb = new StringBuilder();
      for (int position = 0; position < words.size(); position++) {
        String word = words.get(position);
        String tag = tags.get(position);
        sb.append(word);
        sb.append("_");
        sb.append(tag);
      }
      return sb.toString();
    }

    public boolean equals(Object o) {
      if (this == o) return true;
      if (!(o instanceof TaggedSentence)) return false;

      final TaggedSentence taggedSentence = (TaggedSentence) o;

      if (tags != null ? !tags.equals(taggedSentence.tags) : taggedSentence.tags != null) return false;
      if (words != null ? !words.equals(taggedSentence.words) : taggedSentence.words != null) return false;

      return true;
    }

    public int hashCode() {
      int result;
      result = (words != null ? words.hashCode() : 0);
      result = 29 * result + (tags != null ? tags.hashCode() : 0);
      return result;
    }

    public TaggedSentence(List<String> words, List<String> tags) {
      this.words = words;
      this.tags = tags;
    }
  }

  /**
   * States are pairs of tags along with a position index, representing the two
   * tags preceding that position.  So, the START state, which can be gotten by
   * State.getStartState() is [START, START, 0].  To build an arbitrary state,
   * for example [DT, NN, 2], use the static factory method
   * State.buildState("DT", "NN", 2).  There isnt' a single final state, since
   * sentences lengths vary, so State.getEndState(i) takes a parameter for the
   * length of the sentence.
   */
  static class State {

    private static transient Interner<State> stateInterner = new Interner<State>(new Interner.CanonicalFactory<State>() {
      public State build(State state) {
        return new State(state);
      }
    });

    private static transient State tempState = new State();

    public static State getStartState() {
      return buildState(START_TAG, START_TAG, 0);
    }

    public static State getStopState(int position) {
      return buildState(STOP_TAG, STOP_TAG, position);
    }

    public static State buildState(String previousPreviousTag, String previousTag, int position) {
      tempState.setState(previousPreviousTag, previousTag, position);
      return stateInterner.intern(tempState);
    }

    public static List<String> toTagList(List<State> states) {
      List<String> tags = new ArrayList<String>();
      if (states.size() > 0) {
        tags.add(states.get(0).getPreviousPreviousTag());
        for (State state : states) {
          tags.add(state.getPreviousTag());
        }
      }
      return tags;
    }

    public int getPosition() {
      return position;
    }

    public String getPreviousTag() {
      return previousTag;
    }

    public String getPreviousPreviousTag() {
      return previousPreviousTag;
    }

    public State getNextState(String tag) {
      return State.buildState(getPreviousTag(), tag, getPosition() + 1);
    }

    public State getPreviousState(String tag) {
      return State.buildState(tag, getPreviousPreviousTag(), getPosition() - 1);
    }

    public boolean equals(Object o) {
      if (this == o) return true;
      if (!(o instanceof State)) return false;

      final State state = (State) o;

      if (position != state.position) return false;
      if (previousPreviousTag != null ? !previousPreviousTag.equals(state.previousPreviousTag) : state.previousPreviousTag != null) return false;
      if (previousTag != null ? !previousTag.equals(state.previousTag) : state.previousTag != null) return false;

      return true;
    }

    public int hashCode() {
      int result;
      result = position;
      result = 29 * result + (previousTag != null ? previousTag.hashCode() : 0);
      result = 29 * result + (previousPreviousTag != null ? previousPreviousTag.hashCode() : 0);
      return result;
    }

    public String toString() {
      return "[" + getPreviousPreviousTag() + ", " + getPreviousTag() + ", " + getPosition() + "]";
    }

    int position;
    String previousTag;
    String previousPreviousTag;

    private void setState(String previousPreviousTag, String previousTag, int position) {
      this.previousPreviousTag = previousPreviousTag;
      this.previousTag = previousTag;
      this.position = position;
    }

    private State() {
    }

    private State(State state) {
      setState(state.getPreviousPreviousTag(), state.getPreviousTag(), state.getPosition());
    }
  }

  /**
   * A Trellis is a graph with a start state an an end state, along with
   * successor and predecessor functions.
   */
  static class Trellis <S> {
    S startState;
    S endState;
    CounterMap<S, S> forwardTransitions;
    CounterMap<S, S> backwardTransitions;

    /**
     * Get the unique start state for this trellis.
     */
    public S getStartState() {
      return startState;
    }

    public void setStartState(S startState) {
      this.startState = startState;
    }

    /**
     * Get the unique end state for this trellis.
     */
    public S getEndState() {
      return endState;
    }

    public void setStopState(S endState) {
      this.endState = endState;
    }

    /**
     * For a given state, returns a counter over what states can be next in the
     * markov process, along with the cost of that transition.  Caution: a state
     * not in the counter is illegal, and should be considered to have cost
     * Double.NEGATIVE_INFINITY, but Counters score items they don't contain as
     * 0.
     */
    public Counter<S> getForwardTransitions(S state) {
      return forwardTransitions.getCounter(state);

    }


    /**
     * For a given state, returns a counter over what states can precede it in
     * the markov process, along with the cost of that transition.
     */
    public Counter<S> getBackwardTransitions(S state) {
      return backwardTransitions.getCounter(state);
    }

    public void setTransitionCount(S start, S end, double count) {
      forwardTransitions.setCount(start, end, count);
      backwardTransitions.setCount(end, start, count);
    }

    public Trellis() {
      forwardTransitions = new CounterMap<S, S>();
      backwardTransitions = new CounterMap<S, S>();
    }
  }

  /**
   * A TrellisDecoder takes a Trellis and returns a path through that trellis in
   * which the first item is trellis.getStartState(), the last is
   * trellis.getEndState(), and each pair of states is conntected in the
   * trellis.
   */
  static interface TrellisDecoder <S> {
    List<S> getBestPath(Trellis<S> trellis);
  }

  static class GreedyDecoder <S> implements TrellisDecoder<S> {
    public List<S> getBestPath(Trellis<S> trellis) {
      List<S> states = new ArrayList<S>();
      S currentState = trellis.getStartState();
      states.add(currentState);
      while (!currentState.equals(trellis.getEndState())) {
        Counter<S> transitions = trellis.getForwardTransitions(currentState);
        S nextState = transitions.argMax();
        states.add(nextState);
        currentState = nextState;
        System.out.println(currentState);
      }
      return states;
    }
  }

  static class ViterbiDecoder<S> implements TrellisDecoder<S> {

    public List<S> getBestPath(Trellis<S> trellis) {

      // define the OPT array of counters for bigram states
      List<Counter<S>> optArray = new ArrayList<Counter<S>>();
      // define array of back pointers
      List<Map<S,S>> backPointers = new ArrayList<Map<S,S>>();
      // position in the trellis
      int k = 0;
      S startState = trellis.getStartState();
      S endState = trellis.getEndState();

      // set the initial k = 0 scores in the OPT array and backPointers array
      Counter<S> prevTransitions = new Counter<S>();
      prevTransitions.setCount(startState, 1.0); // initialize previous states to only the start state
      // the scores in the transitions counter should all be multiplied by optArray(k=0) as the initial state.
      // but optArray(k=0) is equivalent to 1, so we don't have to do any further computation
      optArray.add(k, prevTransitions);
      // backPointers array doesn't have a value at k=0
      backPointers.add(k, null);


      // start at the beginning.
      boolean endStateReached = false;
      while (!endStateReached) {
        k++;
        optArray.add(k, new Counter<S>());
        backPointers.add(k, new HashMap<S,S>());

        prevTransitions = optArray.get(k-1);

        // for each previous state, where a state is a tag bigram (w,u)
        for (S prevState : prevTransitions.keySet()) {
          // find the max score for the expression score(k1, w, u) * HMM score function
          // in practice, that means we'll have to convert the HMM scores by the following Math.exp(transitions.argMax())
          // pi(k,u,v) = max(pi(k-1,u,v)*q(v|w,u)*e(x|v))
          
          // get score value of pi(k-1,u,v)
          double optScore = prevTransitions.getCount(prevState);

          Counter<S> nextTransitions = trellis.getForwardTransitions(prevState);
          endStateReached |= nextTransitions.containsKey(endState);
          // for each possible next state, where a state is a tag bigram (u,v)
          for (S nextState : nextTransitions.keySet()) {

            // get score value of HMM score q(v|w,u) * e(x|v)
            double nextScore = Math.exp(nextTransitions.getCount(nextState));

            // determine the optimal score and previous state to produce the next state
            double score = optScore * nextScore;
            if (score >= optArray.get(k).getCount(nextState)) {
              // remember the best score in the OPT array
              optArray.get(k).setCount(nextState, score);
              // remember the state that will produce the best score
              backPointers.get(k).put(nextState, prevState);
            }
          }
        }
//System.out.print(k+"~");
      }
//System.out.println("done");

      // backsolve the OPT array
      List<S> states = new ArrayList<S>();
      int i = backPointers.size() - 1;
      S currentState = trellis.getEndState();
      states.add(currentState);
      while (i > 0) {
        currentState = backPointers.get(i).get(currentState);
        states.add(currentState);
        i--;
      }
      Collections.reverse(states);
//System.out.println(states);
      return states;
    }

  }

  static class POSTagger {

    LocalTrigramScorer localTrigramScorer;
    TrellisDecoder<State> trellisDecoder;

    // chop up the training instances into local contexts and pass them on to the local scorer.
    public void train(List<TaggedSentence> taggedSentences) {
      localTrigramScorer.train(extractLabeledLocalTrigramContexts(taggedSentences));
    }

    // chop up the validation instances into local contexts and pass them on to the local scorer.
    public void validate(List<TaggedSentence> taggedSentences) {
      localTrigramScorer.validate(extractLabeledLocalTrigramContexts(taggedSentences));
    }

    private List<LabeledLocalTrigramContext> extractLabeledLocalTrigramContexts(List<TaggedSentence> taggedSentences) {
      List<LabeledLocalTrigramContext> localTrigramContexts = new ArrayList<LabeledLocalTrigramContext>();
      for (TaggedSentence taggedSentence : taggedSentences) {
        localTrigramContexts.addAll(extractLabeledLocalTrigramContexts(taggedSentence));
      }
      return localTrigramContexts;
    }

    private List<LabeledLocalTrigramContext> extractLabeledLocalTrigramContexts(TaggedSentence taggedSentence) {
      List<LabeledLocalTrigramContext> labeledLocalTrigramContexts = new ArrayList<LabeledLocalTrigramContext>();
      List<String> words = new BoundedList<String>(taggedSentence.getWords(), START_WORD, STOP_WORD);
      List<String> tags = new BoundedList<String>(taggedSentence.getTags(), START_TAG, STOP_TAG);
      for (int position = 0; position <= taggedSentence.size() + 1; position++) {
        labeledLocalTrigramContexts.add(new LabeledLocalTrigramContext(words, position, tags.get(position - 2), tags.get(position - 1), tags.get(position)));
      }
      return labeledLocalTrigramContexts;
    }

    /**
     * Builds a Trellis over a sentence, by starting at the state State, and
     * advancing through all legal extensions of each state already in the
     * trellis.  You should not have to modify this code (or even read it,
     * really).
     */
    private Trellis<State> buildTrellis(List<String> sentence) {
      Trellis<State> trellis = new Trellis<State>();
      trellis.setStartState(State.getStartState());
      State stopState = State.getStopState(sentence.size() + 2);
      trellis.setStopState(stopState);
      Set<State> states = Collections.singleton(State.getStartState());
      for (int position = 0; position <= sentence.size() + 1; position++) {
        Set<State> nextStates = new HashSet<State>();
        for (State state : states) {
          if (state.equals(stopState))
            continue;
          LocalTrigramContext localTrigramContext = new LocalTrigramContext(sentence, position, state.getPreviousPreviousTag(), state.getPreviousTag());
          Counter<String> tagScores = localTrigramScorer.getLogScoreCounter(localTrigramContext);
          for (String tag : tagScores.keySet()) {
            double score = tagScores.getCount(tag);
            State nextState = state.getNextState(tag);
            trellis.setTransitionCount(state, nextState, score);
            nextStates.add(nextState);
          }
        }
//        System.out.println("States: "+nextStates);
        states = nextStates;
      }
      return trellis;
    }

    // to tag a sentence: build its trellis and find a path through that trellis
    public List<String> tag(List<String> sentence) {
      Trellis<State> trellis = buildTrellis(sentence);
      List<State> states = trellisDecoder.getBestPath(trellis);
      List<String> tags = State.toTagList(states);
      tags = stripBoundaryTags(tags);
      return tags;
    }

    /**
     * Scores a tagging for a sentence.
     * Calcutating the quantity [Sum over i]log*P(t_i | w_i)
     *
     * Note that a tag sequence not accepted
     * by the markov process should receive a log score of
     * Double.NEGATIVE_INFINITY.
     */
    public double scoreTagging(TaggedSentence taggedSentence) {
      double logScore = 0.0;
      List<LabeledLocalTrigramContext> labeledLocalTrigramContexts = extractLabeledLocalTrigramContexts(taggedSentence);
      for (LabeledLocalTrigramContext labeledLocalTrigramContext : labeledLocalTrigramContexts) {
        Counter<String> logScoreCounter = localTrigramScorer.getLogScoreCounter(labeledLocalTrigramContext);
        String currentTag = labeledLocalTrigramContext.getCurrentTag();
        if (logScoreCounter.containsKey(currentTag)) {
          logScore += logScoreCounter.getCount(currentTag);
        } else {
          logScore += Double.NEGATIVE_INFINITY;
        }
      }
      return logScore;
    }

    private List<String> stripBoundaryTags(List<String> tags) {
      return tags.subList(2, tags.size() - 2);
    }

    public POSTagger(LocalTrigramScorer localTrigramScorer, TrellisDecoder<State> trellisDecoder) {
      this.localTrigramScorer = localTrigramScorer;
      this.trellisDecoder = trellisDecoder;
    }
  }

  /**
   * A LocalTrigramContext is a position in a sentence, along with the previous
   * two tags -- basically a FeatureVector.
   */
  static class LocalTrigramContext {
    List<String> words;
    int position;
    String previousTag;
    String previousPreviousTag;

    public List<String> getWords() {
      return words;
    }

    public String getCurrentWord() {
      return words.get(position);
    }

    public int getPosition() {
      return position;
    }

    public String getPreviousTag() {
      return previousTag;
    }

    public String getPreviousPreviousTag() {
      return previousPreviousTag;
    }

    public String toString() {
      return "[" + getPreviousPreviousTag() + ", " + getPreviousTag() + ", " + getCurrentWord() + "]";
    }

    public LocalTrigramContext(List<String> words, int position, String previousPreviousTag, String previousTag) {
      this.words = words;
      this.position = position;
      this.previousTag = previousTag;
      this.previousPreviousTag = previousPreviousTag;
    }
  }

  /**
   * A LabeledLocalTrigramContext is a context plus the correct tag for that
   * position -- basically a LabeledFeatureVector
   */
  static class LabeledLocalTrigramContext extends LocalTrigramContext {
    String currentTag;

    public String getCurrentTag() {
      return currentTag;
    }

    public String toString() {
      return "[" + getPreviousPreviousTag() + ", " + getPreviousTag() + ", " + getCurrentWord() + "_" + getCurrentTag() + "]";
    }

    public LabeledLocalTrigramContext(List<String> words, int position, String previousPreviousTag, String previousTag, String currentTag) {
      super(words, position, previousPreviousTag, previousTag);
      this.currentTag = currentTag;
    }
  }

  /**
   * LocalTrigramScorers assign scores to tags occuring in specific
   * LocalTrigramContexts.
   */
  static interface LocalTrigramScorer {
    /**
     * The Counter returned should contain log probabilities, meaning if all
     * values are exponentiated and summed, they should sum to one.  For
     * efficiency, the Counter can contain only the tags which occur in the
     * given context with non-zero model probability.
     */
    Counter<String> getLogScoreCounter(LocalTrigramContext localTrigramContext);

    void train(List<LabeledLocalTrigramContext> localTrigramContexts);

    void validate(List<LabeledLocalTrigramContext> localTrigramContexts);
  }

  /**
   * The MostFrequentTagScorer gives each test word the tag it was seen with
   * most often in training (or the tag with the most seen word types if the
   * test word is unseen in training.  This scorer actually does a little more
   * than its name claims -- if constructed with restrictTrigrams = true, it
   * will forbid illegal tag trigrams, otherwise it makes no use of tag history
   * information whatsoever.
   */
  static class MostFrequentTagScorer implements LocalTrigramScorer {

    boolean restrictTrigrams; // if true, assign log score of Double.NEGATIVE_INFINITY to illegal tag trigrams.

    CounterMap<String, String> wordsToTags = new CounterMap<String, String>();
    Counter<String> unknownWordTags = new Counter<String>();
    Set<String> seenTagTrigrams = new HashSet<String>();

    public int getHistorySize() {
      return 2;
    }

    /*
     * Word counter values for the specified word context
     * Calculates  log(P(t|w))
     */
    public Counter<String> getLogScoreCounter(LocalTrigramContext localTrigramContext) {
      int position = localTrigramContext.getPosition();
      String word = localTrigramContext.getWords().get(position);
      Counter<String> tagCounter = unknownWordTags;
      if (wordsToTags.keySet().contains(word)) {
        tagCounter = wordsToTags.getCounter(word);
      }
      Set<String> allowedFollowingTags = allowedFollowingTags(tagCounter.keySet(), localTrigramContext.getPreviousPreviousTag(), localTrigramContext.getPreviousTag());
      Counter<String> logScoreCounter = new Counter<String>();
      for (String tag : tagCounter.keySet()) {
        double logScore = Math.log(tagCounter.getCount(tag));
        if (!restrictTrigrams || allowedFollowingTags.isEmpty() || allowedFollowingTags.contains(tag))
          logScoreCounter.setCount(tag, logScore);
      }
      return logScoreCounter;
    }

    private Set<String> allowedFollowingTags(Set<String> tags, String previousPreviousTag, String previousTag) {
      Set<String> allowedTags = new HashSet<String>();
      for (String tag : tags) {
        String trigramString = makeTrigramString(previousPreviousTag, previousTag, tag);
        if (seenTagTrigrams.contains((trigramString))) {
          allowedTags.add(tag);
        }
      }
      return allowedTags;
    }

    private String makeTrigramString(String previousPreviousTag, String previousTag, String currentTag) {
      return previousPreviousTag + " " + previousTag + " " + currentTag;
    }

    public void train(List<LabeledLocalTrigramContext> labeledLocalTrigramContexts) {
      // collect word-tag counts
      for (LabeledLocalTrigramContext labeledLocalTrigramContext : labeledLocalTrigramContexts) {
        String word = labeledLocalTrigramContext.getCurrentWord();
        String tag = labeledLocalTrigramContext.getCurrentTag();
        if (!wordsToTags.keySet().contains(word)) {
          // word is currently unknown, so tally its tag in the unknown tag counter
          unknownWordTags.incrementCount(tag, 1.0);
        }
        wordsToTags.incrementCount(word, tag, 1.0);
        seenTagTrigrams.add(makeTrigramString(labeledLocalTrigramContext.getPreviousPreviousTag(), labeledLocalTrigramContext.getPreviousTag(), labeledLocalTrigramContext.getCurrentTag()));
      }
      wordsToTags = Counters.conditionalNormalize(wordsToTags);
      unknownWordTags = Counters.normalize(unknownWordTags);
    }

    public void validate(List<LabeledLocalTrigramContext> labeledLocalTrigramContexts) {
      // no tuning for this dummy model!
    }

    public MostFrequentTagScorer(boolean restrictTrigrams) {
      this.restrictTrigrams = restrictTrigrams;
    }
  }

  /**
   * The TrigramHMMScorer gives each test word the tag it was seen with
   * most often in training (or the tag with the most seen word types if the
   * test word is unseen in training.  This scorer actually does a little more
   * than its name claims -- if constructed with restrictTrigrams = true, it
   * will forbid illegal tag trigrams, otherwise it makes no use of tag history
   * information whatsoever.
   */
  static class TrigramHMMScorer implements LocalTrigramScorer {

    private static int MAX_SUFFIX_LENGTH = 5;
    private static int RARE_WORD_COUNT_THRESHOLD = 10;

    boolean restrictTrigrams; // if true, assign log score of Double.NEGATIVE_INFINITY to illegal tag trigrams.

    // maps a tag to a word counter for words seen marked with that tag
    CounterMap<String, String> tagToWordCounters = new CounterMap<String, String>();
    CounterMap<String, String> tagTrigramCounters = new CounterMap<String, String>();
    CounterMap<String, String> tagToSuffixCounters = new CounterMap<String, String>();
    Counter<String> suffixFrequencies = new Counter<String>();
    Counter<String> tagFrequencies = new Counter<String>();
    Set<String> seenTagTrigrams = new HashSet<String>();
    Set<String> seenWords = new HashSet<String>();
    double thetaWeight = 0.0;

    public int getHistorySize() {
      return 2;
    }

    /*
     * Word counter values for the specified word context
     * Calculates   log( P(t_i | t_i-1, t_i-2)*P(w_i | t_i) )
     * where P(t_i | t_i-1, t_i-2)*P(w_i | t_i) is a normalized score distribution over tags
     */
    public Counter<String> getLogScoreCounter(LocalTrigramContext localTrigramContext) {
      int position = localTrigramContext.getPosition();
      String word = localTrigramContext.getWords().get(position);

      // get the 2 previous tags for this context
      String tagBigram = makeBigramString(localTrigramContext.getPreviousPreviousTag(), localTrigramContext.getPreviousTag());
      // get the Counter for tags that have appeared after the 2 previous tags
      Counter<String> trigramCounter = tagTrigramCounters.getCounter(tagBigram);

      // a set of tags to consider as the current tag
      Set<String> possibleNextTags;
      // if this tag bigram has never been seen before
      if (trigramCounter.isEmpty()) {
        // consider all possible tags for the current tag
        possibleNextTags = tagToWordCounters.keySet();
      } else {
        // consider only the tags that were see to come after this tag bigram in the training data
        possibleNextTags = trigramCounter.keySet();
      }

      Counter<String> tagScoreCounter = new Counter<String>();
      // for each possible next tag, calculate a score
      for (String tag : possibleNextTags) {

        // get Counter for the words tagged with this tag
        Counter<String> wordCounter = tagToWordCounters.getCounter(tag);
        
        // score = probability of seeing this tag after the previous 2 tags * probability of seeing the current word given this tag
        double transition = trigramCounter.getCount(tag);
        double emission = 0.0;
        if (seenWords.contains(word)) {
          emission = wordCounter.getCount(word);
        } else {
          // if you don't cut off part of the word, you are effectively using the complete unknown word
          int suffixLength = Math.min(2, word.length() - 1);
          String suffix = word.substring(word.length() - suffixLength, word.length());
          emission = tagToSuffixCounters.getCount(tag, suffix);
//System.out.println(suffix + " ::: "+ wordCounter.getCount(word) + " ---- " +emission);
        }

        // make sure to never Log a value of zero
        transition = Math.log( (transition > 0) ? transition : Double.MIN_VALUE );
        emission = Math.log( (emission > 0) ? emission : Double.MIN_VALUE );

        tagScoreCounter.setCount(tag, (transition + emission) );
      }
      return tagScoreCounter;
    }

    private String makeTrigramString(String previousPreviousTag, String previousTag, String currentTag) {
      return previousPreviousTag + " " + previousTag + " " + currentTag;
    }

    private String makeBigramString(String previousTag, String currentTag) {
      return previousTag + " " + currentTag;
    }

    public void train(List<LabeledLocalTrigramContext> labeledLocalTrigramContexts) {
      CounterMap<String, String> suffixToTagCounters = new CounterMap<String, String>();

      // collect word-tag counts
      for (LabeledLocalTrigramContext labeledLocalTrigramContext : labeledLocalTrigramContexts) {
        String word = labeledLocalTrigramContext.getCurrentWord();
        String tag = labeledLocalTrigramContext.getCurrentTag();
        String tagBigram = makeBigramString(labeledLocalTrigramContext.getPreviousPreviousTag(), labeledLocalTrigramContext.getPreviousTag());

        tagToWordCounters.incrementCount(tag, word, 1.0);
        tagTrigramCounters.incrementCount(tagBigram, tag, 1.0);
        tagFrequencies.incrementCount(tag, 1.0);

        // P(T | ln-i, ... ln)
        // keep track of tag counts conditioned on suffixes of different length
        int suffixLength = Math.min(word.length(), MAX_SUFFIX_LENGTH);
        for (int i = 0; i <= suffixLength; i++) {
          String suffix = word.substring(word.length() - i, word.length());
          suffixToTagCounters.incrementCount(suffix, tag, 1.0);
          suffixFrequencies.incrementCount(suffix, 1.0);
        }

        seenWords.add(word);
      }

      
      // Turn this into a probability distribution
      tagFrequencies = Counters.normalize(tagFrequencies);
      suffixFrequencies = Counters.normalize(suffixFrequencies);
      suffixToTagCounters = Counters.conditionalNormalize(suffixToTagCounters);

      // calculate theta weight for recursive suffix smoothing
      double freqSum = 0.0;
      double tagFreqAvg = 1.0 / tagFrequencies.size();
      for (String tag : tagFrequencies.keySet()) {
        freqSum += Math.pow((tagFrequencies.getCount(tag) - tagFreqAvg), 2.0);
      }
      thetaWeight = freqSum / (tagFrequencies.size() - 1);
      
      // prepare to smooth the suffix distributions
      Queue<String> sortedSuffixes = new PriorityQueue<String>(
        suffixToTagCounters.keySet().size(),
        new Comparator<String>() {
          @Override
          // shortest suffix first
          public int compare(String s1, String s2) {
            return s1.length() - s2.length();
          }
        }
      );
      sortedSuffixes.addAll(suffixToTagCounters.keySet());

      // actually smooth the suffix distributions
      CounterMap<String, String> smoothedSuffixToTagCounters = new CounterMap<String, String>();
      while (!sortedSuffixes.isEmpty()) {
        String suffix = sortedSuffixes.poll();
        Counter<String> oldTagCounter = suffixToTagCounters.getCounter(suffix);

        // a suffix of one letter less
        String preSuffix = (suffix.length() > 1) ? suffix.substring(1, suffix.length()) : null;
        
        for (String tag : oldTagCounter.keySet()) {

          if (preSuffix == null) {
            // we have no suffix, set it to an initialization value (the frequency)
            smoothedSuffixToTagCounters.setCount(suffix, tag, tagFrequencies.getCount(tag));
          } else {
            // calculate a smoothed score
            double smoothedScore = oldTagCounter.getCount(tag);
            smoothedScore += (thetaWeight * smoothedSuffixToTagCounters.getCount(preSuffix, tag));
            smoothedScore /= (1 + thetaWeight);
            smoothedSuffixToTagCounters.setCount(suffix, tag, smoothedScore);
          }
        }
      }
      suffixToTagCounters = smoothedSuffixToTagCounters;
      smoothedSuffixToTagCounters = null;

      // want our distribution to be P(suffix | tag)
      // however, suffixToTagCounters represents P(tag | suffix)
      // so we have to use bayes rule
      for (String suffix : suffixToTagCounters.keySet()) {
        Counter<String> tagCounter = suffixToTagCounters.getCounter(suffix);
        for (String tag : tagCounter.keySet()) {
          double bayesResult = tagCounter.getCount(tag);
          bayesResult *= suffixFrequencies.getCount(suffix);
          bayesResult /= tagFrequencies.getCount(tag);

          tagToSuffixCounters.setCount(tag, suffix, bayesResult);
        }
      }

      tagToSuffixCounters = Counters.conditionalNormalize(tagToSuffixCounters);
      tagToWordCounters = Counters.conditionalNormalize(tagToWordCounters);
      tagTrigramCounters = Counters.conditionalNormalize(tagTrigramCounters);
    }

    public void validate(List<LabeledLocalTrigramContext> labeledLocalTrigramContexts) {
      // no tuning for this dummy model!
    }

    public TrigramHMMScorer(boolean restrictTrigrams) {
      this.restrictTrigrams = restrictTrigrams;
    }
  }

  private static List<TaggedSentence> readTaggedSentences(String path, int low, int high) {
    Collection<Tree<String>> trees = PennTreebankReader.readTrees(path, low, high);
    List<TaggedSentence> taggedSentences = new ArrayList<TaggedSentence>();
    Trees.TreeTransformer<String> treeTransformer = new Trees.EmptyNodeStripper();
    for (Tree<String> tree : trees) {
      tree = treeTransformer.transformTree(tree);
      List<String> words = new BoundedList<String>(new ArrayList<String>(tree.getYield()), START_WORD, STOP_WORD);
      List<String> tags = new BoundedList<String>(new ArrayList<String>(tree.getPreTerminalYield()), START_TAG, STOP_TAG);
      taggedSentences.add(new TaggedSentence(words, tags));
    }
    return taggedSentences;
  }

  private static void evaluateTagger(POSTagger posTagger, List<TaggedSentence> taggedSentences, Set<String> trainingVocabulary, boolean verbose) {
    double numTags = 0.0;
    double numTagsCorrect = 0.0;
    double numUnknownWords = 0.0;
    double numUnknownWordsCorrect = 0.0;
    int numDecodingInversions = 0;
    for (TaggedSentence taggedSentence : taggedSentences) {
      List<String> words = taggedSentence.getWords();
      List<String> goldTags = taggedSentence.getTags();
      List<String> guessedTags = posTagger.tag(words);
      for (int position = 0; position < words.size() - 1; position++) {
        String word = words.get(position);
        String goldTag = goldTags.get(position);
        String guessedTag = guessedTags.get(position);
        if (guessedTag.equals(goldTag))
          numTagsCorrect += 1.0;
        numTags += 1.0;
        if (!trainingVocabulary.contains(word)) {
          if (guessedTag.equals(goldTag))
            numUnknownWordsCorrect += 1.0;
          numUnknownWords += 1.0;
        }
      }
      double scoreOfGoldTagging = posTagger.scoreTagging(taggedSentence);
      double scoreOfGuessedTagging = posTagger.scoreTagging(new TaggedSentence(words, guessedTags));
      if (scoreOfGoldTagging > scoreOfGuessedTagging) {
        numDecodingInversions++;
        if (verbose) System.out.println("WARNING: Decoder suboptimality detected.  Gold tagging has higher score than guessed tagging.");
      }
      if (verbose) System.out.println(alignedTaggings(words, goldTags, guessedTags, true) + "\n");
    }
    System.out.println("Tag Accuracy: " + (numTagsCorrect / numTags) + " (Unknown Accuracy: " + (numUnknownWordsCorrect / numUnknownWords) + ")  Decoder Suboptimalities Detected: " + numDecodingInversions);
  }

  // pretty-print a pair of taggings for a sentence, possibly suppressing the tags which correctly match
  private static String alignedTaggings(List<String> words, List<String> goldTags, List<String> guessedTags, boolean suppressCorrectTags) {
    StringBuilder goldSB = new StringBuilder("Gold Tags: ");
    StringBuilder guessedSB = new StringBuilder("Guessed Tags: ");
    StringBuilder wordSB = new StringBuilder("Words: ");
    for (int position = 0; position < words.size(); position++) {
      equalizeLengths(wordSB, goldSB, guessedSB);
      String word = words.get(position);
      String gold = goldTags.get(position);
      String guessed = guessedTags.get(position);
      wordSB.append(word);
      if (position < words.size() - 1)
        wordSB.append(' ');
      boolean correct = (gold.equals(guessed));
      if (correct && suppressCorrectTags)
        continue;
      guessedSB.append(guessed);
      goldSB.append(gold);
    }
    return goldSB + "\n" + guessedSB + "\n" + wordSB;
  }

  private static void equalizeLengths(StringBuilder sb1, StringBuilder sb2, StringBuilder sb3) {
    int maxLength = sb1.length();
    maxLength = Math.max(maxLength, sb2.length());
    maxLength = Math.max(maxLength, sb3.length());
    ensureLength(sb1, maxLength);
    ensureLength(sb2, maxLength);
    ensureLength(sb3, maxLength);
  }

  private static void ensureLength(StringBuilder sb, int length) {
    while (sb.length() < length) {
      sb.append(' ');
    }
  }

  private static Set<String> extractVocabulary(List<TaggedSentence> taggedSentences) {
    Set<String> vocabulary = new HashSet<String>();
    for (TaggedSentence taggedSentence : taggedSentences) {
      List<String> words = taggedSentence.getWords();
      vocabulary.addAll(words);
    }
    return vocabulary;
  }

  public static void main(String[] args) {
    // Parse command line flags and arguments
    Map<String, String> argMap = CommandLineUtils.simpleCommandLineParser(args);

    // Set up default parameters and settings
    String basePath = ".";
    boolean verbose = false;
    boolean useValidation = true;

    // Update defaults using command line specifications

    // The path to the assignment data
    if (argMap.containsKey("-path")) {
      basePath = argMap.get("-path");
    }
    System.out.println("Using base path: " + basePath);

    // Whether to use the validation or test set
    if (argMap.containsKey("-test")) {
      String testString = argMap.get("-test");
      if (testString.equalsIgnoreCase("test"))
        useValidation = false;
    }
    System.out.println("Testing on: " + (useValidation ? "validation" : "test"));

    // Whether or not to print the individual errors.
    if (argMap.containsKey("-verbose")) {
      verbose = true;
    }

    // Read in data
    System.out.print("Loading training sentences...");
    List<TaggedSentence> trainTaggedSentences = readTaggedSentences(basePath, 200, 2199);
    Set<String> trainingVocabulary = extractVocabulary(trainTaggedSentences);
    System.out.println("done.");
    System.out.print("Loading validation sentences...");
    List<TaggedSentence> validationTaggedSentences = readTaggedSentences(basePath, 2200, 2299);
    System.out.println("done.");
    System.out.print("Loading test sentences...");
    List<TaggedSentence> testTaggedSentences = readTaggedSentences(basePath, 2300, 2399);
    System.out.println("done.");

    // Construct tagger components
    // TODO : improve on the upgraded scorer
    LocalTrigramScorer localTrigramScorer = new TrigramHMMScorer(true);
    // TODO : improve on the GreedyDecoder
    TrellisDecoder<State> trellisDecoder = new ViterbiDecoder<State>();

    // Train tagger
    POSTagger posTagger = new POSTagger(localTrigramScorer, trellisDecoder);
    posTagger.train(trainTaggedSentences);
    posTagger.validate(validationTaggedSentences);

    // Test tagger
    evaluateTagger(posTagger,
                   (useValidation ? validationTaggedSentences : testTaggedSentences),
                   trainingVocabulary,
                   verbose);
  }
}
