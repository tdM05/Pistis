# problems
### LLM maps a whole thing as comm when it may contain a def.
- But how really do we tell the difference between comm and containing somethign important? like the high level stuff still talks about math, just they are not the "base case" math things.

# Procedure
- level 0 faithflu or not
- level 1: split 5-20 segments -> for each categorize and for each non-comm box, say faithful or not.
- level 2: for each non comm, split 5-20 segmetyns -> for each categorize and for each non-comm box, faithful or not....

# the question we ansewr
Interested in studying this align-then-label at differnet levels. what are the effects? is more levels strictly better and finds same faithfulness errors as the level 0? btw level 0 is just naive llm? are they disjoint between levels the errors? is more level always better in terms of # actual errors? of the unfaithfluness found, what % is acutally unfaithful. requires human eval.

perhaps we can plot unfaithfulness precision vs level and plot (PR) # actually faithful errors found vs level (NUM). We don't do recall since finding all unfaithfulness errors ourselves is out of scope.

- do both plots incrase in level? how?
- how to evaluate true positive? we can do outside llm for now to check each if it is an actual thing to get rough idea? ideally we should do human eval perhaps 3 people per thing. Expect around

# the point of this work
align-then-label paper is promising way to formalize faithfulness but it is not general for an entire paper. this generalizes that and answers how good it is with naive llm for precision and number of faithfulness issues.

if precision is high for some level N, then we can claim this to be a valid tool, idealy N>0 so we can say this tool is better than naive llm. in some sense we are finding the optimal N.

# how much human work needed?
roughly 2 faithfulness errors per level and 10 segments per level would be roughly $10^{(l-1)} \times 2$ unfaithfulness things to check for humans. that may grow out of control. we'll see emprically.

# RQS
### How does level j compare to level k under the same llm thinking budget? cause if k>j, k surely has more thinking time and that could be the simple reason. is it more thinking time or is it something else?

### Which level is optimal in precision, and which is optimal in accuracy?

### Is knowing this level and it having this high precision and this high accuracy useful in practice? for example on the openai results?
this could be like some qualitative analysis of human found fiathfulnes errors and we can provide an estimate based on precision of lower bound of faithfulness errors, and we already identify where to look so that is nice.