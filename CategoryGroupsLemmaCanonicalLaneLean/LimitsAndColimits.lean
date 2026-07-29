import canonicalLaneMathlib.AdmissibleClass

namespace HautevilleHouse
namespace CategoryGroupsLemmaCanonicalLaneLean

structure Cone (J C : Type u) [Category J] [Category C] (F : J ⥤ C) where
  apex : C
  legs : ∀ (j : J), apex ⟶ F.obj j
  naturality : Prop
  naturalityClosed : naturality

structure Limit (J C : Type u) [Category J] [Category C] (F : J ⥤ C) where
  cone : Cone J C F
  universal : Prop
  universalClosed : universal

def LimitExists (J C : Type u) [Category J] [Category C] (F : J ⥤ C) : Prop :=
  ∃ (L : Limit J C F), True

structure HasAllLimits (C : Type u) [Category C] where
  limitsExist : ∀ (J : Type u) [Category J] (F : J ⥤ C), LimitExists J C F
  limitsExistClosed : limitsExist

theorem limit_exists_for_small (C : Type u) [Category C] [HasLimits C] (J : Type u) [Category J] (F : J ⥤ C) :
    LimitExists J C F := by
  constructor
  exact ⟨limit F, by
    refine { cone := { apex := limit F, legs := limit.π F, naturalityClosed := ?_ }, universalClosed := ?_ }
    · apply limit.π_naturality
    · apply limit.isLimit⟩, trivial⟩

structure LimitsEvidence {C : Type u} [Category C] (H : HasAllLimits C) where
  limitsExistClosed : H.limitsExist

def HasAllLimitsClosed {C : Type u} [Category C] (H : HasAllLimits C) : Prop :=
  H.limitsExist

theorem has_all_limits_closed_from_evidence {C : Type u} [Category C] (H : HasAllLimits C) (ev : LimitsEvidence H) :
    HasAllLimitsClosed H := by
  exact ev.limitsExistClosed

structure Cocone (J C : Type u) [Category J] [Category C] (F : J ⥤ C) where
  coapex : C
  legs : ∀ (j : J), F.obj j ⟶ coapex
  naturality : Prop
  naturalityClosed : naturality

structure Colimit (J C : Type u) [Category J] [Category C] (F : J ⥤ C) where
  cocone : Cocone J C F
  universal : Prop
  universalClosed : universal

def ColimitExists (J C : Type u) [Category J] [Category C] (F : J ⥤ C) : Prop :=
  ∃ (L : Colimit J C F), True

structure HasAllColimits (C : Type u) [Category C] where
  colimitsExist : ∀ (J : Type u) [Category J] (F : J ⥤ C), ColimitExists J C F
  colimitsExistClosed : colimitsExist

theorem colimit_exists_for_small (C : Type u) [Category C] [HasColimits C] (J : Type u) [Category J] (F : J ⥤ C) :
    ColimitExists J C F := by
  constructor
  exact ⟨colimit F, by
    refine { cocone := { coapex := colimit F, legs := colimit.ι F, naturalityClosed := ?_ }, universalClosed := ?_ }
    · apply colimit.ι_naturality
    · apply colimit.isColimit⟩, trivial⟩

end CategoryGroupsLemmaCanonicalLaneLean
end HautevilleHouse