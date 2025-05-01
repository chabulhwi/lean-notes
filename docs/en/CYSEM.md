# Redefining child or youth sexual exploitation material (CYSEM)

## Act On the Protection of Children and Youth Against Sex Offenses

The current South Korean Act On the Protection of Children and Youth Against Sex
Offenses (아동·청소년의 성보호에 관한 법률) defines **child or youth sexual
exploitation materials (CYSEM)** as follows:

> Article 2 (Definitions) The terms used in this Act are defined as follows:
> \<Amended on Dec. 18, 2012; Jan. 28, 2014; Jan. 16, 2018; May 19, 2020; Jun.
> 2, 2020; Mar. 23, 2021; Mar. 26, 2024; Oct. 16, 2024\>
> 
> 1. The term "children or youth" means persons under 19 years of age;
> …
> 5. The term "child or youth sexual exploitation materials" means depiction of
>    children or youth, or persons or representations that can be obviously
>    perceived as children or youth, doing any act defined in any item of
>    subparagraph 4 or engaging in any other sexual act, in the form of a film,
>    video, game software, or picture, image, etc. displayed on computers, or
>    other communications media;

#### Items of subparagraph 4

\(a\) Sexual intercourse; \
\(b\) Pseudo-sexual intercourse using part of the body, such as the mouth and
      anus, or implements; \
\(c\) Contacting or exposing all or part of the body, which causes sexual
      humiliation or repugnance of ordinary people; \
\(d\) Masturbation;

## Redefining CYSEM

I wrote a [document][rdf] about how to revise the definition of child or youth
sexual exploitation material (CYSEM) in my Git repository called
[`talks`][talks].

Here are the changes I made to the definition:

(a) I clarified that CYSEM doesn't include written text.
(b) I included printed media in CYSEM that uses real minors. However, CYSEM
    depicting cartoon characters still doesn't include printed matter.
(c) I explicitly stated that CYSEM that uses fictional characters lacks serious
    literary, artistic, ideological, scientific, medical, or educational value.

Here, I present a formalization of the following arguments I made:

1. Virtual CYSEM, which only uses adults or fictional characters, is *by
   definition* obscene. Therefore, it lacks any value.
2. The current definition of CYSEM is logically equivalent to my definition,
   where it is defined as (a) real CYSEM or (b) virtual CYSEM that lacks any
   value.

I also formally stated my conjecture about a visual depiction of a child or
youth doing a sexual act: there's no such depiction that isn't obscene.

## Some important premises of my arguments

Below are some important premises of my arguments.

1. Virtual CYSEM is CYSEM.
2. CYSEM is equivalent to child or youth pornography (CYP).
3. CYP is pornography.
4. Pornography is obscene.
5. Any obscene material lacks any value.

I formalized each of these premises as follows:

1. `isCYSEM_of_isVirtualCYSEM {d : D} (h : IsVirtualCYSEM d) : IsCYSEM d`
2. `isCYSEM_iff_isCYP {d : D} : IsCYSEM d ↔ IsCYP d`
3. `isPorn_of_isCYP {d : D} (h : IsCYP d) : IsPorn d`
4. `isObscene_of_isPorn {d : D} (h : IsPorn d) : IsObscene d`
5. `lacksValue_of_isObscene {d : D} (h : IsObscene d) : LacksValue d`

These theorems are contained in the `Depiction` namespace.

## References

* Act On the Protection of Children and Youth Against Sex Offenses. Act No.
  20462, Oct. 16, 2024.
  <https://elaw.klri.re.kr/kor_service/lawView.do?hseq=68811&lang=KOR>.

[rdf]: https://git.sr.ht/~chabulhwi/talks/tree/master/item/redefining-child-or-youth-sexual-exploitation-materials.md
[talks]: https://git.sr.ht/~chabulhwi/talks
