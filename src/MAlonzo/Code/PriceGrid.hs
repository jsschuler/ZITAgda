{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

module MAlonzo.Code.PriceGrid where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Fin.Properties
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.Integer.GCD
import qualified MAlonzo.Code.Data.Integer.Properties
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Nat.GCD
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Rational.Base
import qualified MAlonzo.Code.Data.Rational.Properties
import qualified MAlonzo.Code.Surplus

-- PriceGrid.ratio
d_ratio_4 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6
d_ratio_4 v0 v1
  = coe
      MAlonzo.Code.Data.Rational.Base.du__'47'__156
      (coe MAlonzo.Code.Data.Fin.Base.du_toℕ_18 (coe v1))
      (coe addInt (coe (1 :: Integer)) (coe v0))
-- PriceGrid.ratioNonNeg
d_ratioNonNeg_14 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_ratioNonNeg_14 v0 v1
  = coe
      MAlonzo.Code.Data.Rational.Properties.du_nonNegative'8315''185'_3992
      (coe d_ratio_4 (coe v0) (coe v1))
-- PriceGrid.ratioLeOne
d_ratioLeOne_30 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_ratioLeOne_30 v0 v1
  = coe
      MAlonzo.Code.Data.Rational.Base.C_'42''8804''42'_60
      (d_final_66 (coe v0) (coe v1))
-- PriceGrid._.m
d_m_40 :: Integer -> MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> Integer
d_m_40 ~v0 v1 = du_m_40 v1
du_m_40 :: MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> Integer
du_m_40 v0 = coe MAlonzo.Code.Data.Fin.Base.du_toℕ_18 (coe v0)
-- PriceGrid._.d
d_d_42 :: Integer -> MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> Integer
d_d_42 v0 ~v1 = du_d_42 v0
du_d_42 :: Integer -> Integer
du_d_42 v0 = coe addInt (coe (1 :: Integer)) (coe v0)
-- PriceGrid._.g
d_g_44 :: Integer -> MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> Integer
d_g_44 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.GCD.d_gcd_152 (coe du_m_40 (coe v1))
      (coe du_d_42 (coe v0))
-- PriceGrid._.G
d_G_46 :: Integer -> MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> Integer
d_G_46 v0 v1
  = coe
      MAlonzo.Code.Data.Integer.GCD.d_gcd_136 (coe du_m_40 (coe v1))
      (coe du_d_42 (coe v0))
-- PriceGrid._.g≢0
d_g'8802'0_48 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_g'8802'0_48 = erased
-- PriceGrid._.G-pos
d_G'45'pos_50 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134
d_G'45'pos_50 v0 v1
  = coe
      MAlonzo.Code.Data.Integer.Base.du_positive_220
      (coe
         MAlonzo.Code.Data.Integer.Base.C_'43''60''43'_72
         (coe
            MAlonzo.Code.Data.Nat.Properties.du_n'8802'0'8658'n'62'0_3232
            (coe d_g_44 (coe v0) (coe v1))))
-- PriceGrid._.N
d_N_52 :: Integer -> MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> Integer
d_N_52 v0 v1
  = coe
      MAlonzo.Code.Data.Rational.Base.d_numerator_14
      (coe d_ratio_4 (coe v0) (coe v1))
-- PriceGrid._.D
d_D_54 :: Integer -> MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> Integer
d_D_54 v0 v1
  = coe
      MAlonzo.Code.Data.Rational.Base.d_denominator_22
      (coe d_ratio_4 (coe v0) (coe v1))
-- PriceGrid._.eq-N
d_eq'45'N_56 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eq'45'N_56 = erased
-- PriceGrid._.eq-D
d_eq'45'D_58 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eq'45'D_58 = erased
-- PriceGrid._.m≤d
d_m'8804'd_60 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_m'8804'd_60 ~v0 v1 = du_m'8804'd_60 v1
du_m'8804'd_60 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
du_m'8804'd_60 v0
  = coe
      MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
         (coe MAlonzo.Code.Data.Fin.Properties.du_toℕ'60'n_156 (coe v0)))
-- PriceGrid._.NG≤DG
d_NG'8804'DG_62 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_NG'8804'DG_62 ~v0 v1 = du_NG'8804'DG_62 v1
du_NG'8804'DG_62 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
du_NG'8804'DG_62 v0 = coe du_m'8804'd_60 (coe v0)
-- PriceGrid._.N≤D
d_N'8804'D_64 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_N'8804'D_64 v0 v1
  = coe
      MAlonzo.Code.Data.Integer.Properties.du_'42''45'cancel'691''45''8804''45'pos_6064
      (coe d_N_52 (coe v0) (coe v1)) (coe d_D_54 (coe v0) (coe v1))
      (coe du_NG'8804'DG_62 (coe v1))
-- PriceGrid._.final
d_final_66 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_final_66 v0 v1 = coe d_N'8804'D_64 (coe v0) (coe v1)
-- PriceGrid.tick
d_tick_70 ::
  Integer ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6
d_tick_70 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Rational.Base.d__'42'__276 (coe v1)
      (coe d_ratio_4 (coe v0) (coe v2))
-- PriceGrid.tickNonNeg
d_tickNonNeg_84 ::
  Integer ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_tickNonNeg_84 v0 v1 v2 ~v3 = du_tickNonNeg_84 v0 v1 v2
du_tickNonNeg_84 ::
  Integer ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
du_tickNonNeg_84 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Rational.Properties.du_nonNegative'8315''185'_3992
      (coe d_tick_70 (coe v0) (coe v1) (coe v2))
-- PriceGrid.tickLeOneCap
d_tickLeOneCap_110 ::
  Integer ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_tickLeOneCap_110 v0 v1 v2 ~v3 = du_tickLeOneCap_110 v0 v1 v2
du_tickLeOneCap_110 ::
  Integer ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
du_tickLeOneCap_110 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Rational.Properties.du_'42''45'mono'737''45''8804''45'nonNeg_5204
      v1 (d_ratio_4 (coe v0) (coe v2))
      MAlonzo.Code.Data.Rational.Base.d_1ℚ_180
      (d_ratioLeOne_30 (coe v0) (coe v2))
-- PriceGrid.buyerTick
d_buyerTick_130 ::
  Integer ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6
d_buyerTick_130 v0 v1 v2 v3
  = coe
      d_tick_70 (coe v0)
      (coe
         MAlonzo.Code.Data.Rational.Base.d__'8851'__332 (coe v1) (coe v2))
      (coe v3)
-- PriceGrid.buyerTickBelowValuation
d_buyerTickBelowValuation_148 ::
  Integer ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_buyerTickBelowValuation_148 v0 v1 v2 v3 ~v4
  = du_buyerTickBelowValuation_148 v0 v1 v2 v3
du_buyerTickBelowValuation_148 ::
  Integer ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
du_buyerTickBelowValuation_148 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Rational.Properties.d_'8804''45'trans_3608
      (d_buyerTick_130 (coe v0) (coe v1) (coe v2) (coe v3))
      (MAlonzo.Code.Data.Rational.Base.d__'8851'__332 (coe v1) (coe v2))
      v1
      (coe
         du_tickLeOneCap_110 (coe v0)
         (coe
            MAlonzo.Code.Data.Rational.Base.d__'8851'__332 (coe v1) (coe v2))
         (coe v3))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'x_2924
         (coe
            MAlonzo.Code.Data.Rational.Properties.d_'8804''45'totalPreorder_3646)
         (coe
            MAlonzo.Code.Data.Rational.Properties.d_'8851''45'operator_5716)
         (coe v1) (coe v2))
-- PriceGrid.buyerTickWithinBudget
d_buyerTickWithinBudget_168 ::
  Integer ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_buyerTickWithinBudget_168 v0 v1 v2 v3 ~v4
  = du_buyerTickWithinBudget_168 v0 v1 v2 v3
du_buyerTickWithinBudget_168 ::
  Integer ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
du_buyerTickWithinBudget_168 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Rational.Properties.d_'8804''45'trans_3608
      (d_buyerTick_130 (coe v0) (coe v1) (coe v2) (coe v3))
      (MAlonzo.Code.Data.Rational.Base.d__'8851'__332 (coe v1) (coe v2))
      v2
      (coe
         du_tickLeOneCap_110 (coe v0)
         (coe
            MAlonzo.Code.Data.Rational.Base.d__'8851'__332 (coe v1) (coe v2))
         (coe v3))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'y_2950
         (coe
            MAlonzo.Code.Data.Rational.Properties.d_'8804''45'totalPreorder_3646)
         (coe
            MAlonzo.Code.Data.Rational.Properties.d_'8851''45'operator_5716)
         (coe v1) (coe v2))
-- PriceGrid.sellerTick
d_sellerTick_182 ::
  Integer ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6
d_sellerTick_182 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Rational.Base.d__'43'__270 (coe v1)
      (coe
         MAlonzo.Code.Data.Rational.Base.d__'42'__276
         (coe
            MAlonzo.Code.Data.Rational.Base.d__'45'__282 (coe v2) (coe v1))
         (coe d_ratio_4 (coe v0) (coe v3)))
-- PriceGrid.p≤p+q
d_p'8804'p'43'q_196 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_p'8804'p'43'q_196 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Rational.Properties.d_'43''45'mono'691''45''8804'_4384
      (coe v0) (coe MAlonzo.Code.Data.Rational.Base.d_0ℚ_178) (coe v1)
      (coe v2)
-- PriceGrid.sellerTickAboveValuation
d_sellerTickAboveValuation_214 ::
  Integer ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_sellerTickAboveValuation_214 v0 v1 v2 v3 ~v4
  = du_sellerTickAboveValuation_214 v0 v1 v2 v3
du_sellerTickAboveValuation_214 ::
  Integer ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
du_sellerTickAboveValuation_214 v0 v1 v2 v3
  = coe
      d_p'8804'p'43'q_196 (coe v1)
      (coe
         MAlonzo.Code.Data.Rational.Base.d__'42'__276
         (coe
            MAlonzo.Code.Data.Rational.Base.d__'45'__282 (coe v2) (coe v1))
         (coe d_ratio_4 (coe v0) (coe v3)))
      (coe du_product'8805'0_236 (coe v0) (coe v1) (coe v2) (coe v3))
-- PriceGrid._.spread≥0
d_spread'8805'0_230 ::
  Integer ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_spread'8805'0_230 ~v0 v1 v2 ~v3 v4
  = du_spread'8805'0_230 v1 v2 v4
du_spread'8805'0_230 ::
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
du_spread'8805'0_230 v0 v1 v2
  = coe
      MAlonzo.Code.Surplus.d_p'8804'q'8658'0'8804'q'45'p_6 (coe v0)
      (coe v1) (coe v2)
-- PriceGrid._.product≥0
d_product'8805'0_236 ::
  Integer ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
d_product'8805'0_236 v0 v1 v2 v3 ~v4
  = du_product'8805'0_236 v0 v1 v2 v3
du_product'8805'0_236 ::
  Integer ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Rational.Base.T_ℚ_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Rational.Base.T__'8804'__54
du_product'8805'0_236 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Rational.Properties.du_nonNegative'8315''185'_3992
      (coe
         MAlonzo.Code.Data.Rational.Base.d__'42'__276
         (coe
            MAlonzo.Code.Data.Rational.Base.d__'45'__282 (coe v2) (coe v1))
         (coe d_ratio_4 (coe v0) (coe v3)))
