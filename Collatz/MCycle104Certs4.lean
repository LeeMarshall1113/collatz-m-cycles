import Collatz.MCycle104Certs3

/-!
# Certificates of the listed shapes of `data104`, chunks 12..15
-/

set_option Elab.async false

namespace Collatz

theorem certs104_12 : certsOK3 104 20 grid103 grid3_105 data104.certs shapes104_12 = true := by
  decide +kernel

theorem certs104_13 : certsOK3 104 20 grid103 grid3_105 data104.certs shapes104_13 = true := by
  decide +kernel

theorem certs104_14 : certsOK3 104 20 grid103 grid3_105 data104.certs shapes104_14 = true := by
  decide +kernel

theorem certs104_15 : certsOK3 104 20 grid103 grid3_105 data104.certs shapes104_15 = true := by
  decide +kernel

end Collatz
