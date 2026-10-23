import Collatz.MCycle110Certs106

/-!
# Certificates of the listed shapes of `data110`, chunks 424..427
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs110_424 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_424 = true := by
  decide +kernel

theorem certs110_425 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_425 = true := by
  decide +kernel

theorem certs110_426 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_426 = true := by
  decide +kernel

theorem certs110_427 : certsOK3 110 20 grid110 grid3_107 data110.certs shapes110_427 = true := by
  decide +kernel

end Collatz
