import Collatz.MCycle104Certs4

/-!
# Certificates of the listed shapes of `data104`, chunks 16..19
-/

set_option Elab.async false

namespace Collatz

theorem certs104_16 : certsOK3 104 20 grid103 grid3_105 data104.certs shapes104_16 = true := by
  decide +kernel

theorem certs104_17 : certsOK3 104 20 grid103 grid3_105 data104.certs shapes104_17 = true := by
  decide +kernel

theorem certs104_18 : certsOK3 104 20 grid103 grid3_105 data104.certs shapes104_18 = true := by
  decide +kernel

theorem certs104_19 : certsOK3 104 20 grid103 grid3_105 data104.certs shapes104_19 = true := by
  decide +kernel

end Collatz
