import Collatz.MCycle105Certs1

/-!
# Certificates of the listed shapes of `data105`, chunks 4..7
-/

set_option Elab.async false

namespace Collatz

theorem certs105_4 : certsOK3 105 20 grid103 grid3_105 data105.certs shapes105_4 = true := by
  decide +kernel

theorem certs105_5 : certsOK3 105 20 grid103 grid3_105 data105.certs shapes105_5 = true := by
  decide +kernel

theorem certs105_6 : certsOK3 105 20 grid103 grid3_105 data105.certs shapes105_6 = true := by
  decide +kernel

theorem certs105_7 : certsOK3 105 20 grid103 grid3_105 data105.certs shapes105_7 = true := by
  decide +kernel

end Collatz
