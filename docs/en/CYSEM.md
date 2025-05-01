# Redefining child or youth sexual exploitation material (CYSEM)

## Act On the Protection of Children and Youth Against Sex Offenses

The current South Korean Act On the Protection of Children and Youth Against Sex
Offenses (Act No. 20462, Oct. 16, 2024) defines **child or youth sexual
exploitation materials (CYSEM)** as follows:

> Article 2 (Definitions) The terms used in this Act are defined as follows:
> \<Amended on Dec. 18, 2012; Jan. 28, 2014; Jan. 16, 2018; May 19, 2020; Jun.
> 2, 2020; Mar. 23, 2021; Mar. 26, 2024; Oct. 16, 2024\>
> 
> 1\. The term "children or youth" means persons under 19 years of age; \
> … \
> 5\. The term "child or youth sexual exploitation materials" means depiction of
>     children or youth, or persons or representations that can be obviously
>     perceived as children or youth, doing any act defined in any item of
>     subparagraph 4 or engaging in any other sexual act, in the form of a film,
>     video, game software, or picture, image, etc. displayed on computers, or
>     other communications media;

Below are the items of subparagraph 4:

> \(a\) Sexual intercourse; \
> \(b\) Pseudo-sexual intercourse using part of the body, such as the mouth and
>       anus, or implements; \
> \(c\) Contacting or exposing all or part of the body, which causes sexual
>       humiliation or repugnance of ordinary people; \
> \(d\) Masturbation;

## Redefining CYSEM

I wrote a [document][rdf] (Korean) about how to revise the definition of child
or youth sexual exploitation material (CYSEM).

I suggested three changes to subparagraph 5 of Article 2:

1. I clarified that CYSEM doesn't include written text.
2. I included printed media in CYSEM that uses real children or youth. However,
   CYSEM using cartoon characters still doesn't include printed matter.
3. I explicitly stated that CYSEM that uses fictional characters lacks serious
   literary, artistic, ideological, scientific, medical, or educational value.

In the [`CYSEM`][CYSEM] file, I used the Lean theorem prover to formalize the
following assertions:

1. Virtual CYSEM, which only uses adults or fictional characters, is *by
   definition* obscene. (`Depiction.isObscene_of_isVirtualCYSEM`)
2. Virtual CYSEM lacks any value. (`Depiction.lacksValue_of_isVirtualCYSEM`)
3. Apart from the changes to subparagraph 4 of Article 2, the current definition
   of CYSEM is logically equivalent to my definition, where it is defined as (a)
   real CYSEM or (b) virtual CYSEM that lacks any value.
   (`Depiction.isCYSEM_iff_isRealCYSEM_or_isVirtualCYSEM_and_lacksValue`)

I also formally stated my conjecture about a visual depiction of a real child or
youth doing a sexual act: all of them are obscene.
(`ObsceneVisualDepiction.real_childOrYouth_conjecture`)

## Important premises and lemmas

Below are some important premises and lemmas.

### Important premises

1. Every obscene material lacks any value. (`Depiction.lacksValue_of_isObscene`)
2. Pornography is obscene. (`Depiction.isObscene_of_isPorn`)
3. CYSEM is equivalent to CYP. (`Depiction.isCYSEM_iff_isCYP`)

### Important lemmas

1. Child or youth pornography (CYP) is pornography.
   (`Depiction.isPorn_of_isCYP`)
2. Virtual CYSEM is CYSEM. (`Depiction.isCYSEM_of_isVirtualCYSEM`)

## References

* Act On the Protection of Children and Youth Against Sex Offenses. Act No.
  20462, Oct. 16, 2024.
  <https://elaw.klri.re.kr/kor_service/lawView.do?hseq=68811&lang=KOR>.

[rdf]: https://git.sr.ht/~chabulhwi/talks/tree/master/item/redefining-child-or-youth-sexual-exploitation-materials.md
[CYSEM]: ../../Notes/CYSEM.lean
