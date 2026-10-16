# should we enforce coverage and order at every level?
This is a key design question. On one hand, more freedom allows the mapping to be more generalizable. On the other hand, the more human-manual effort is required to check with more degrees of freedom. 

For example in statements: $x$ satisifes P, for every $x \in \mathbb{R}$. If order is enforced, this *cannot compile* in lean, as $x \in \mathbb{R}$ would need to be declared *first* before satisfying property P. 

Now a natural question is *should we be this strict?*. On one hand, a pedantic person may say yes, and another may say no since ths is used a lot. But we can have slightly worse versions that just do not make sense, so it is more question of how loose we wanna be.

So we *need* a more expressive framewok like that in faithalign where spans may not even be continuous, may not need to cover everything, may not be in order etc.

But the problem with this is that with what I will call *First Order Pistis*, i.e.e the one in the Pistis paper, *order* did not have to be checked seperately as there is a strict rule, same for coveraged for example. without enforcing these, an oracle would need to decide if for example, not including this part in coverage is valid, or these things in different order is valid etc. There is more effort on oracle. 

So I'm thinking we can have a few versions of Pistis *First-Order Pistis* is the most strict case, then slightly less strict one could be *Second-Order Pistis* etc.

This can be combined with K-Pistis to be like *First Order K-Pistis* for example.7y76