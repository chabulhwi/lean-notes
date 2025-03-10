# 안셀무스의 존재론적 논증

[`Anselm`][anselm] 파일이 아마 린 커뮤니티에서 신의 존재에 대한 존재론적 논증을 형식화하려는 ~~[첫 번째][fst]~~ 두 번째 시도인 듯합니다. 이 파일은 앨빈 플랜팅가가 정식화한 안셀무스의 존재론적 논증을 수정한 버전입니다. (스탠퍼드 철학 백과사전의 ['존재론적 논증'](#참고-문헌) 항목의 [9.1 정식화 1][plantinga]을 보십시오.)

1. 신은 지성에 존재하지만, 현실에는 존재하지 않는다. (**귀류법**을 위한 가정)
2. 현실에 존재함이 지성에만 존재함보다 크다. (전제)
3. 생각될 수 있는 존재자가 현실에 존재한다. (**수정된** 전제)
4. 현실에 존재하고 생각될 수 있는 존재자는 신보다 크다. [(1)과 (2)에 따름]
5. 생각될 수 있고 신보다 큰 존재자가 존재한다.
[(3)과 (4)에 따름]
6. 신보다 큰 어떤 존재자도 생각될 수 없다. ('신'의 정의에 따름)
7. 그러므로 신이 지성에는 존재하지만 현실에는 존재하지 않는다는 것은 거짓이다. [(1), (5), (6)에 따름]
8. 신은 지성에 존재한다. (어리석은 이도 동의하는 전제)
9. 그러므로 신은 현실에 존재한다. [(7), (8)에 따름]

논증의 세 전제는 다음과 같이 형식화했습니다.

* `lt_of_inUnderstanding_not_inReality_inReality {x y : Being} :
InUnderstanding x → ¬InReality x → InReality y → x < y` (2단계)
* `exists_conceivable_and_inReality : ∃ (x : Being), Conceivable x ∧
InReality x` (3단계)
* `IsGod.inUnderstanding {x : Being} : IsGod x → InUnderstanding x` (8단계)

앨빈 플랜팅가가 정식화한 원래 논증의 3단계는 다음 전제입니다. "신의 모든 속성을 갖고 현실에 존재하는 존재자는 생각될 수 있다." 이 전제는 불필요합니다. 신은 생각될 수 있는 가장 큰 존재자이므로, 신 그 자체는 생각될 수 있습니다.
따라서 신의 모든 속성을 갖는 존재자는 생각될 수 있습니다.

제가 보건대, 안셀무스가 제시한 논증의 결론은 다음 진술과 같습니다.

```lean
theorem IsGod.inReality {x : Being} : IsGod x → InReality x
```

이 정리는 신이 현실에 존재한다고 진술하지 않습니다. 어느 한 존재자가 신이면 그 존재자는 현실에 존재한다는 얘기만 할 뿐입니다. 신이 현실에 존재함을 증명하려면, `∃ (x : Being), IsGod x ∧ InReality x`임을 보여야 합니다.

이런 이유로, 저는 안셀무스의 논증이 신의 존재를 보이지 않는다고 생각합니다. 물론 제가 안셀무스의 논증을 잘못 형식화했을 수 있습니다.

## 정리 `not_exists_int_isGod`

`∃ (x : Being), IsGod x ∧ InReality x`라는 진술은, 안셀무스가 제시한 논증의 전제(그리고 린의 유형론의 공리)로 공리계가 이뤄진 이론의 정리가 아님을 제가 증명하지 않았다는 [지적을 받았습니다][owl]. 이 지적은 한국의 철학 포럼인 서강올빼미의 한 이용자 카르납(car_nap) 님이 했습니다.

그래서 `not_exists_int_isGod`이라는 정리를 증명했습니다. 이 정리는 `∃ (x : Being), IsGod x`이라는 진술이 거짓인 유형 세계 단계 `u`, 유형 `Being : Type u` 그리고 `Anselm Being`의 사례[인스턴스]가 존재함을 보여 줍니다.

## 참고 문헌

* Oppy, Graham, "Ontological Arguments", *The Stanford Encyclopedia of
Philosophy* (Fall 2023 Edition), Edward N. Zalta & Uri Nodelman (eds.),
URL =
<https://plato.stanford.edu/archives/fall2023/entries/ontological-arguments/>.

## 감사의 말

### 린 커뮤니티

에릭 위저 님과 앨리스터 터커 님에게 감사의 말씀을 드리고 싶습니다. 에릭 위저 님은 제 초고와 둘째 원고의 모순성을 찾아냈습니다. 앨리스터 터커 님은 앨빈 플랜팅가가 정식화한 원래 논증의 3단계를 린으로 옮길 방법을 논했습니다. 이분들과의 논의는 [이 링크][leanzulip]에서 볼 수 있습니다.

안셀무스가 제시한 논증의 전제와 린의 유형론의 공리에서 `∃ (x : Being), IsGod x ∧ InReality x`라는 진술을 도출할 수 없음을 증명하는 방법은 앨리스터 터커 님이 제게 [알려 줬습니다][tucker].

### 서강올빼미

[위에서 언급한 문제](#정리-anselmnot_exists_int_isgod)를 제기한 카르납 님에게 감사합니다.

[anselm]: ../../Notes/Anselm.lean
[fst]: https://github.com/forked-from-1kasper/ground_zero/blob/9f83f7c6224eee8905b16aeebc4c234b4b216031/GroundZero/Theorems/Ontological.lean#L520-L521
[plantinga]: https://plato.stanford.edu/entries/ontological-arguments/#StAnsOntArg
[owl]: https://forum.owlofsogang.com/t/lean/3613/9
[leanzulip]: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Formalizing.20St.2E.20Anselm's.20ontological.20argument/near/39867934
[tucker]: https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/how.20do.20I.20say.20.22a.20sentence.20is.20a.20theorem.20of.20a.20theory.22.20in.20lean.3F/near/399042805
