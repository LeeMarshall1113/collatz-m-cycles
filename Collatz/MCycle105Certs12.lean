import Collatz.MCycle105Certs11

/-!
# Certificates of the listed shapes of `data105`, chunks 44..46
-/

set_option Elab.async false

namespace Collatz

theorem certs105_44 : certsOK3 105 20 grid103 grid3_105 data105.certs shapes105_44 = true := by
  decide +kernel

theorem certs105_45 : certsOK3 105 20 grid103 grid3_105 data105.certs shapes105_45 = true := by
  decide +kernel

theorem certs105_46 : certsOK3 105 20 grid103 grid3_105 data105.certs shapes105_46 = true := by
  decide +kernel

end Collatz
