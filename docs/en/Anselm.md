# St. Anselm's ontological argument

The [`Anselm`][0] file might be the first attempt in the Lean community to formalize an
ontological argument for the existence of God in Lean. It's a modified
version of the formulation of St. Anselm's ontological argument by Alvin
Plantinga. (See [9.1 Formulation 1 of the SEP entry "Ontological
Arguments."][1])

1. God exists in the understanding but not in reality. (Assumption for
   *reductio*)
2. Existence in reality is greater than existence in the understanding
   alone. (Premise)
3. There exists a being in reality that can be conceived. (*Modified*
   premise)
4. A being that exists in reality and can be conceived is greater than
   God. (From (1) and (2).)
5. There exists a being that can be conceived and is greater than God.
   (From (3) and (4).)
6. No being greater than God can be conceived. (From the definition of
   “God”.)
7. Hence, it is false that God exists in the understanding but not in
   reality. (From (1), (5), (6).)
8. God exists in the understanding. (Premise, to which even the Fool
   agrees.)
9. Hence God exists in reality. (From (7), (8).)

Step 3 of the original formulation by Alvin Plantinga is the following
premise: "A being having all of God’s properties plus existence in
reality can be conceived." This premise is redundant. Since God is the
greatest being that can be conceived, God itself can be conceived.
Therefore, a being having all of God's properties can be conceived.

I think we can only conclude from St. Anselm's argument that the
following statement is true:

```lean
theorem isGod_inReality {x : Being} : isGod x → inReality x
```

This theorem doesn't state that God exists in reality. It merely says
that if a being is God, it exists in reality. In order to prove the
existence of God in reality, you need to show that `∃ (x : Being),
isGod x ∧ inReality x`.

For this reason, I think St. Anselm's argument doesn't show God's
existence. Of course, I might have formalized it wrong.

## Reference

Oppy, Graham, "Ontological Arguments", *The Stanford Encyclopedia of
Philosophy* (Fall 2023 Edition), Edward N. Zalta & Uri Nodelman (eds.),
URL = <https://plato.stanford.edu/archives/fall2023/entries/ontological-arguments/>.

## Acknowledgements

I'd like to thank Eric Wieser and Alistair Tucker. Eric Wieser found
inconsistency in my first and second drafts. Alistair Tucker gave a
comment on transcribing premise 3 of the original formulation by Alvin
Plantinga. You can see my discussion with them in [this link][2].

[0]: ../../Notes/Anselm.lean
[1]: https://plato.stanford.edu/entries/ontological-arguments/#StAnsOntArg
[2]: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Formalizing.20St.2E.20Anselm's.20ontological.20argument/near/39867934
