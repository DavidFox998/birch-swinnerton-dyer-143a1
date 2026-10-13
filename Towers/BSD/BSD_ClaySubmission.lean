import Towers.BSD.MathlibGaps.FrobeniusDiscriminant_CLOSED
import Towers.BSD.MathlibGaps.LFunctionIsLinFunc_CLOSED

theorem BSD_ClaySubmission_Combinator :=
  And.intro
    Towers.BSD.MathlibGaps.BSD_HasseBound_Discriminant_CLOSED
    Towers.BSD.MathlibGaps.BSD_LFunctionIsLinFunc_CLOSED
