/*=======================================================================================*/
/*  This Sail RISC-V architecture model, comprising all files and                        */
/*  directories except where otherwise noted is subject the BSD                          */
/*  two-clause license in the LICENSE file.                                              */
/*                                                                                       */
/*  SPDX-License-Identifier: BSD-2-Clause                                                */
/*=======================================================================================*/

/* ******************************************************************************* */
/* This file implements the vector Dot-Product Extension: Zvqdotq                  */
/*********************************************************************************/

/* ******************************* OPMVV (VVTYPE) ******************************** */
union clause ast = MVVTYPE : (mvvfunct6, bits(1), vregidx, vregidx, vregidx)

mapping encdec_mvvfunct6 : mvvfunct6 <-> bits(6) = {
  MVV_VQDOT       <-> 0b101100,
  MVV_VQDOTU      <-> 0b101000,
  MVV_VQDOTSU     <-> 0b101010
}

mapping clause encdec = VVTYPE(funct6, vm, vs2, vs1, vd)
  <-> encdec_vvfunct6(funct6) @ vm @ encdec_vreg(vs2) @ encdec_vreg(vs1) @ 0b000 @ encdec_vreg(vd) @ 0b1010111
  when extensionEnabled(Ext_V)

function clause execute(MVVTYPE(funct6, vm, vs2, vs1, vd)) = {
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = get_num_elem(LMUL_pow, SEW);

  // Check if SEW is not equal to 32
  if SEW != 32 then {
    // Only SEW = 32 is supported
    print("SEW is not equal to 32");
    return RETIRE_FAIL
  }

  let 'n = num_elem;
  let 'm = SEW; // 32

  let vm_val  : bits('n)            = read_vmask(num_elem, vm, zvreg);
  let vd_val  : vector('n, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vd);

  let (initial_result, mask) = init_masked_result(num_elem, SEW, LMUL_pow, vd_val, vm_val);
  var result = initial_result;

  foreach (i from 0 to (num_elem - 1)) {
    if mask[i] == bitone then {
      let {a0 @ a1 @ a2 @ a3} : bits(4 * 8) = get_velem(vs2, SEW, i);
      let {b0 @ b1 @ b2 @ b3} : bits(4 * 8) = get_velem(vs1, SEW, i);
      let acc : bits(SEW) = get_velem(vd, SEW, i);

      // Conditionally sign extend based on the instruction type
      if funct6 == MVV_VQDOT or funct6 == MVV_VQDOTSU then {
        a0 = sign_extend(a0);
        a1 = sign_extend(a1);
        a2 = sign_extend(a2);
        a3 = sign_extend(a3);
      }
      if funct6 == MVV_VQDOT or funct6 == MVV_VQDOTUS then {
        b0 = sign_extend(b0);
        b1 = sign_extend(b1);
        b2 = sign_extend(b2);
        b3 = sign_extend(b3);
      }

      let res : bits(SEW) = a0 * b0 + a1 * b1 + a2 * b2 + a3 * b3 + acc;
      result[i] = res;
    }
  }

  write_vreg(num_elem, SEW, LMUL_pow, vd, result);
  set_vstart(zeros());
  RETIRE_SUCCESS
}

  mapping mvvtype_mnemonic : mvvfunct6 <-> string = {
    MVV_VQDOT       <-> "vqdot.vv",
    MVV_VQDOTU      <-> "vqdotu.vv",
    MVV_VQDOTSU     <-> "vqdotsu.vv"
   }

mapping clause assembly = MVVTYPE(funct6, vm, vs2, vs1, vd)
  <-> mvvtype_mnemonic(funct6) ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ sep() ^ vreg_name(vs1) ^ maybe_vmask(vm)

/* ******************************* OPMVX (VXTYPE) ******************************** */
union clause ast = MVXTYPE : (mvxfunct6, bits(1), vregidx, regidx, vregidx)


mapping encdec_mvxfunct6 : mvxfunct6 <-> bits(6) = {
  MVX_VQDOT       <-> 0b101100,
  MVX_VQDOTU      <-> 0b101000,
  MVX_VQDOTSU     <-> 0b101010,
  MVX_VQDOTUS     <-> 0b101110
}

mapping clause encdec = MVXTYPE(funct6, vm, vs2, rs1, vd)
  <-> encdec_mvxfunct6(funct6) @ vm @ encdec_vreg(vs2) @ encdec_reg(rs1) @ 0b110 @ encdec_vreg(vd) @ 0b1010111
  when extensionEnabled(Ext_V)

function clause execute(MVXTYPE(funct6, vm, vs2, vs1, vd)) = {
  let SEW      = get_sew();
  let LMUL_pow = get_lmul_pow();
  let num_elem = get_num_elem(LMUL_pow, SEW);

  // Check if SEW is not equal to 32
  if SEW != 32 then {
    // Only SEW = 32 is supported
    print("SEW is not equal to 32");
    return RETIRE_FAIL
  }

  let 'n = num_elem;
  let 'm = SEW; // 32

  let vm_val  : bits('n)            = read_vmask(num_elem, vm, zvreg);
  let vd_val  : vector('n, bits('m)) = read_vreg(num_elem, SEW, LMUL_pow, vd);

  let (initial_result, mask) = init_masked_result(num_elem, SEW, LMUL_pow, vd_val, vm_val);
  var result = initial_result;

  foreach (i from 0 to (num_elem - 1)) {
    if mask[i] == bitone then {
      let {a0 @ a1 @ a2 @ a3} : bits(4 * 8) = get_velem(vs2, SEW, i);
      let {b0 @ b1 @ b2 @ b3} : bits(4 * 8) = replicate(get_scalar(rs1, 8), 4);

      let acc : bits(SEW) = get_velem(vd_val, i);

      // Conditionally sign extend based on the instruction type
      if funct6 == MVX_VQDOT or funct6 == MVX_VQDOTSU then {
        a0 = sign_extend(a0);
        a1 = sign_extend(a1);
        a2 = sign_extend(a2);
        a3 = sign_extend(a3);
      }
      if funct6 == MVX_VQDOT or funct6 == MVX_VQDOTUS then {
        b0 = sign_extend(b0);
        b1 = sign_extend(b1);
        b2 = sign_extend(b2);
        b3 = sign_extend(b3);
      }

      let res : bits(SEW) = a0 * b0 + a1 * b1 + a2 * b2 + a3 * b3 + acc;
      result[i] = res;
    }
  }

  write_vreg(num_elem, SEW, LMUL_pow, vd, result);
  set_vstart(zeros());
  RETIRE_SUCCESS
}

mapping mvxtype_mnemonic : mvxfunct6 <-> string = {
    MVX_VQDOT       <-> "vqdot.vx",
    MVX_VQDOTU      <-> "vqdotu.vx",
    MVX_VQDOTSU     <-> "vqdotsu.vx",
    MVX_VQDOTUS     <-> "vqdotus.vx"
   }

mapping clause assembly = MVXTYPE(funct6, vm, vs2, rs1, vd)
  <-> mvxtype_mnemonic(funct6) ^ spc() ^ vreg_name(vd) ^ sep() ^ vreg_name(vs2) ^ sep() ^ reg_name(rs1) ^ maybe_vmask(vm)
