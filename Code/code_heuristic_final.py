import sys
import random
import itertools
from dataclasses import dataclass
from enum import Enum
from typing import List, Optional, Tuple
from collections import Counter

# ===== 하이퍼파라미터 =====
UPPER_SOFT_BONUS = 1200
BID_SOFT_COST = 0.18
BID_BUCKETS = [0, 1000, 1750, 2500, 3500, 5000, 7000, 10000, 13000]
BID_BUCKETS_R1 = [0, 1000, 1750]
TIE_DELTA = 1000
HIGH_DIFF_PUSH = 14000

# CHOICE 조기 패널티
CHOICE_EARLY_PENALTY_EARLY = 4200
CHOICE_EARLY_PENALTY_LATE  = 2000

# STASH 가중
STASH_WEIGHT_EARLY = 0.36
STASH_WEIGHT_LATE  = 0.12
STASH_TRIPLE = 900
STASH_QUAD   = 1800
STASH_TWO_PAIR = 500
STASH_SS_MISS1 = 600
STASH_LS_MISS1 = 1100
STASH_UPPER_COVER_BASE = 650

# UPPER 구조대(막판)
def rescue_loss_tolerance(rounds_left: int) -> int:
    if rounds_left <= 2: return 2500
    if rounds_left <= 3: return 2200
    return 1800

# Low face(1/2/3) 스케줄링
LOWFACE_MINCOUNT = 2
LOWFACE_BONUS_PER_COUNT = 700
CHOICE_EXTRA_PENALTY_LOWFACE = 2200

# === TB2/TB4 임계 ===
R1_TB_THRESH = 600
ZEROISH_OBJ_THRESH = 600
ZEROISH_SC_THRESH  = 600
MICROISH_OBJ_THRESH = 700
MICROISH_SC_THRESH  = 700
MICROISH_STEPS = [750, 1000, 1250, 1750, 2500]

# === TB5(aggrish) 임계 ===
AGGRISH_CONTEST = 0.60   # 경쟁률
AGGRISH_AGGR    = 0.60   # 추정 공격성
AGGRISH_STRONG_OBJ = 900 # 전개 obj 강우위
AGGRISH_STRONG_SC  = 900 # 즉시 점수 강우위

def say(s: str):
    print(s, flush=True)

# ===== 카테고리 =====
class DiceRule(Enum):
    ONE = 0
    TWO = 1
    THREE = 2
    FOUR = 3
    FIVE = 4
    SIX = 5
    CHOICE = 6
    FOUR_OF_A_KIND = 7
    FULL_HOUSE = 8
    SMALL_STRAIGHT = 9
    LARGE_STRAIGHT = 10
    YACHT = 11

UPPER = [DiceRule.ONE, DiceRule.TWO, DiceRule.THREE, DiceRule.FOUR, DiceRule.FIVE, DiceRule.SIX]
COMBO = [DiceRule.CHOICE, DiceRule.FOUR_OF_A_KIND, DiceRule.FULL_HOUSE, DiceRule.SMALL_STRAIGHT, DiceRule.LARGE_STRAIGHT, DiceRule.YACHT]

# ===== 점수 함수 =====
def score_upper(d: List[int], face: int) -> int:
    return sum(x for x in d if x == face) * 1000

def score_choice(d: List[int]) -> int:
    return sum(d) * 1000

def score_four_of_a_kind(d: List[int]) -> int:
    c = Counter(d)
    return sum(d) * 1000 if any(v >= 4 for v in c.values()) else 0

def score_full_house(d: List[int]) -> int:
    counts = sorted(Counter(d).values())
    return sum(d) * 1000 if counts == [2, 3] else 0

def score_small_straight(d: List[int]) -> int:
    s = set(d)
    return 15000 if ({1,2,3,4}.issubset(s) or {2,3,4,5}.issubset(s) or {3,4,5,6}.issubset(s)) else 0

def score_large_straight(d: List[int]) -> int:
    s = set(d)
    return 30000 if (s == {1,2,3,4,5} or s == {2,3,4,5,6}) else 0

def score_yacht(d: List[int]) -> int:
    return 50000 if len(set(d)) == 1 else 0

def score_by_rule(d: List[int], r: DiceRule) -> int:
    if r in UPPER: return score_upper(d, r.value + 1)
    if r == DiceRule.CHOICE: return score_choice(d)
    if r == DiceRule.FOUR_OF_A_KIND: return score_four_of_a_kind(d)
    if r == DiceRule.FULL_HOUSE: return score_full_house(d)
    if r == DiceRule.SMALL_STRAIGHT: return score_small_straight(d)
    if r == DiceRule.LARGE_STRAIGHT: return score_large_straight(d)
    if r == DiceRule.YACHT: return score_yacht(d)
    return 0

# ===== 유틸 =====
def multiset_ok(hand: List[int], take: List[int]) -> bool:
    h = Counter(hand); t = Counter(take)
    for k, v in t.items():
        if h[k] < v: return False
    return True

def remove_multiset_safe(bag: List[int], take: List[int]) -> None:
    need = Counter(take)
    i = 0
    while i < len(bag):
        v = bag[i]
        if need.get(v, 0) > 0:
            need[v] -= 1
            bag.pop(i)
        else:
            i += 1

def best_rule_and_score_exact(dice5: List[int], available_rules: List[DiceRule], upper_progress=0) -> Tuple[DiceRule, int]:
    best_r = available_rules[0] if available_rules else DiceRule.CHOICE
    best_sc = -1
    for r in available_rules:
        sc = score_by_rule(dice5, r)
        if r in UPPER and upper_progress < 63000:
            sc += UPPER_SOFT_BONUS
        if sc > best_sc:
            best_sc = sc
            best_r = r
    return best_r, max(best_sc, 0)

def is_threat_rule(rule: DiceRule) -> bool:
    return rule in (DiceRule.YACHT, DiceRule.LARGE_STRAIGHT, DiceRule.FOUR_OF_A_KIND)

def threat_score(rule: DiceRule) -> int:
    if rule == DiceRule.YACHT: return 3
    if rule == DiceRule.LARGE_STRAIGHT: return 2
    if rule == DiceRule.FOUR_OF_A_KIND: return 1
    return 0

# ===== STASH 품질(남은 카테고리 반영) =====
def straight_miss1_score(s: set, available_rules: List[DiceRule]) -> int:
    score = 0
    if DiceRule.SMALL_STRAIGHT in available_rules:
        for T in ({1,2,3,4}, {2,3,4,5}, {3,4,5,6}):
            if len(set(T) - s) == 1:
                score += STASH_SS_MISS1
    if DiceRule.LARGE_STRAIGHT in available_rules:
        for T in ({1,2,3,4,5}, {2,3,4,5,6}):
            if len(set(T) - s) == 1:
                score += STASH_LS_MISS1
    return score

def stash_potential(left5: List[int], available_rules: List[DiceRule]) -> int:
    c = Counter(left5)
    vals = list(c.values())
    s = set(left5)
    pot = 0
    if DiceRule.FOUR_OF_A_KIND in available_rules and any(v >= 4 for v in vals):
        pot += STASH_QUAD
    if DiceRule.FULL_HOUSE in available_rules:
        if any(v >= 3 for v in vals):
            pot += STASH_TRIPLE
        pair_cnt = sum(1 for v in vals if v >= 2)
        if pair_cnt >= 2:
            pot += STASH_TWO_PAIR
    pot += straight_miss1_score(s, available_rules)
    return pot

def stash_upper_coverage(left5: List[int], available_rules: List[DiceRule]) -> int:
    open_upper_faces = {r.value + 1 for r in available_rules if r in UPPER}
    if not open_upper_faces:
        return 0
    covered = len([v for v in left5 if v in open_upper_faces])
    return covered * STASH_UPPER_COVER_BASE

# --- Upper 드라이브 보너스 ---
def upper_drive_extra(rule: DiceRule, put5: List[int], rounds_left: int, upper_progress: int, available_rules: List[DiceRule]) -> int:
    if rule not in UPPER:
        return 0
    face = rule.value + 1
    cnt = put5.count(face)
    sc = score_upper(put5, face)
    slots_left_after = sum(1 for r in available_rules if r in UPPER and r != rule)
    deficit_after = max(0, 63000 - (upper_progress + sc))
    extra = 0
    if cnt >= 3:
        extra += (face * 450) * (cnt - 2)
    if slots_left_after > 0:
        target = deficit_after / max(1, slots_left_after)
        if sc >= 0.75 * target:
            extra += 1800
    if rounds_left > 6 and upper_progress < 48000:
        extra += 1000
    if face <= 3 and cnt >= LOWFACE_MINCOUNT:
        extra += (cnt - LOWFACE_MINCOUNT + 1) * LOWFACE_BONUS_PER_COUNT
    return int(extra)

# ===== PUT 선택 =====
def best_put_with_stash(hand10: List[int], available_rules: List[DiceRule], rounds_left: int, upper_progress: int) -> Tuple[DiceRule, List[int]]:
    if len(hand10) < 5:
        top5 = sorted(hand10, reverse=True)[:5]
        r = DiceRule.CHOICE if DiceRule.CHOICE in available_rules else (available_rules[0] if available_rules else DiceRule.CHOICE)
        return r, top5

    weight = STASH_WEIGHT_EARLY if rounds_left > 6 else STASH_WEIGHT_LATE
    choice_penalty = CHOICE_EARLY_PENALTY_EARLY if (rounds_left > 6 and upper_progress < 48000) else CHOICE_EARLY_PENALTY_LATE

    cnts = Counter(hand10)
    lowface_trigger = any(cnts.get(face, 0) >= LOWFACE_MINCOUNT for face in (1, 2, 3))

    best_obj = -10**12
    best_r, best_put5 = None, None

    idxs = list(range(len(hand10)))
    for comb in itertools.combinations(idxs, 5):
        put5 = [hand10[i] for i in comb]
        left = list(hand10)
        for v in put5:
            left.remove(v)

        pot = stash_potential(left, available_rules) + stash_upper_coverage(left, available_rules)

        for r in available_rules:
            sc = score_by_rule(put5, r)
            obj = sc
            if r in UPPER and upper_progress < 63000:
                obj += UPPER_SOFT_BONUS
                obj += upper_drive_extra(r, put5, rounds_left, upper_progress, available_rules)
            if r == DiceRule.CHOICE and rounds_left > 5:
                obj -= choice_penalty
                if lowface_trigger:
                    obj -= CHOICE_EXTRA_PENALTY_LOWFACE
            obj += int(weight * pot)

            if obj > best_obj:
                best_obj = obj
                best_r = r
                best_put5 = put5

    best_r, best_put5, _ = rescue_upper_late(
        hand10=hand10,
        picked_rule=best_r,
        picked_put5=best_put5,
        best_obj=best_obj,
        available_rules=available_rules,
        rounds_left=rounds_left,            # <-- FIXED
        upper_progress=upper_progress
    )
    return best_r, best_put5

def rescue_upper_late(hand10: List[int],
                      picked_rule: DiceRule,
                      picked_put5: List[int],
                      best_obj: int,
                      available_rules: List[DiceRule],
                      rounds_left: int,
                      upper_progress: int) -> Tuple[DiceRule, List[int], int]:
    tol = rescue_loss_tolerance(rounds_left)
    if rounds_left > 4 or picked_rule is None or picked_put5 is None:
        return picked_rule, picked_put5, best_obj

    open_upper = [r for r in available_rules if r in UPPER]
    if not open_upper:
        return picked_rule, picked_put5, best_obj

    idxs = list(range(len(hand10)))
    best_alt_rule, best_alt_put5, best_alt_obj = None, None, -10**9

    for r in open_upper:
        face = r.value + 1
        for comb in itertools.combinations(idxs, 5):
            put5 = [hand10[i] for i in comb]
            sc = score_upper(put5, face)
            if sc < 3000:
                continue

            left = list(hand10)
            for v in put5: left.remove(v)
            pot = stash_potential(left, available_rules) + stash_upper_coverage(left, available_rules)

            obj = sc
            if upper_progress < 63000:
                obj += UPPER_SOFT_BONUS
                obj += upper_drive_extra(r, put5, rounds_left, upper_progress, available_rules)

            obj += int((STASH_WEIGHT_EARLY if rounds_left > 6 else STASH_WEIGHT_LATE) * pot)

            if obj > best_alt_obj:
                best_alt_obj = obj
                best_alt_rule = r
                best_alt_put5 = put5

    if best_alt_rule is not None and (best_obj - best_alt_obj) <= tol:
        return best_alt_rule, best_alt_put5, best_alt_obj
    return picked_rule, picked_put5, best_obj

# ===== hand10 즉시 PUT 전개 가치 (입찰 보조용) =====
def compute_best_put_obj(hand10: List[int], available_rules: List[DiceRule],
                         rounds_left: int, upper_progress: int) -> Tuple[int, int]:
    if len(hand10) < 5:
        top5 = sorted(hand10, reverse=True)[:5]
        r = DiceRule.CHOICE if DiceRule.CHOICE in available_rules else (available_rules[0] if available_rules else DiceRule.CHOICE)
        sc = score_by_rule(top5, r)
        return sc, sc

    weight = STASH_WEIGHT_EARLY if rounds_left > 6 else STASH_WEIGHT_LATE
    choice_penalty = CHOICE_EARLY_PENALTY_EARLY if (rounds_left > 6 and upper_progress < 48000) else CHOICE_EARLY_PENALTY_LATE

    best_obj, best_sc = -10**12, -1
    cnts_total = Counter(hand10)
    lowface_trigger = any(cnts_total.get(face, 0) >= LOWFACE_MINCOUNT for face in (1,2,3))
    idxs = range(len(hand10))

    for comb in itertools.combinations(idxs, 5):
        put5 = [hand10[i] for i in comb]
        left = list(hand10)
        for v in put5: left.remove(v)

        pot = stash_potential(left, available_rules) + stash_upper_coverage(left, available_rules)

        for r in available_rules:
            sc = score_by_rule(put5, r)
            obj = sc
            if r in UPPER and upper_progress < 63000:
                obj += UPPER_SOFT_BONUS + upper_drive_extra(r, put5, rounds_left, upper_progress, available_rules)
            if r == DiceRule.CHOICE and rounds_left > 5:
                obj -= choice_penalty
                if lowface_trigger:
                    obj -= CHOICE_EXTRA_PENALTY_LOWFACE
            obj += int(weight * pot)
            if obj > best_obj:
                best_obj, best_sc = obj, sc
    return best_obj, best_sc

# ===== EV 기반 입찰 =====
def nearest_bucket(v: float, buckets: List[int]) -> int:
    return min(buckets, key=lambda b: abs(b - v))

def next_bucket_above(v: float, buckets: List[int]) -> int:
    bigger = [b for b in sorted(set(buckets)) if b > v]
    return bigger[0] if bigger else max(buckets)

def ev_resolve(u_des: int, u_alt: int, q_conflict: float, my_b: int, opp_b: int) -> float:
    if my_b > opp_b:
        ev_conf = (u_des - my_b)
    elif my_b < opp_b:
        ev_conf = (u_alt + my_b)
    else:
        ev_conf = 0.5 * (u_des - my_b) + 0.5 * (u_alt + my_b)
    ev_noconf = (u_des - my_b)
    return q_conflict * ev_conf + (1.0 - q_conflict) * ev_noconf

def choose_bid(A: List[int], B: List[int], my_carry: List[int],
               available_rules: List[DiceRule],
               round_no: int, upper_progress: int, rounds_left: int,
               opp_aggr: float, non_got_cnt: int, bid_rounds_cnt: int) -> Tuple[str, int]:

    # hand10 보조(obj/score)
    objA, scA = compute_best_put_obj(my_carry + A, available_rules, rounds_left, upper_progress)
    objB, scB = compute_best_put_obj(my_carry + B, available_rules, rounds_left, upper_progress)

    contest_rate = (non_got_cnt / bid_rounds_cnt) if bid_rounds_cnt > 0 else 0.0
    zeroish_opp  = (opp_aggr <= 0.12 and contest_rate < 0.2 and round_no >= 2)
    microish_opp = (opp_aggr <= 0.55 and 0.2 < contest_rate <= 0.6 and round_no <= 7)
    aggrish_opp  = (opp_aggr >= AGGRISH_AGGR or contest_rate >= AGGRISH_CONTEST)

    # R1: stash/커버 차이로 1000 확정(대칭)
    if round_no == 1:
        valA = stash_potential(A, available_rules) + stash_upper_coverage(A, available_rules)
        valB = stash_potential(B, available_rules) + stash_upper_coverage(B, available_rules)
        diff = valA - valB
        if diff > R1_TB_THRESH:  return ('A', 1000)
        if -diff > R1_TB_THRESH: return ('B', 1000)
        return ('A', 0)

    # zeroish: TB2 유지
    if zeroish_opp:
        if (objB - objA > ZEROISH_OBJ_THRESH) and (scB - scA > ZEROISH_SC_THRESH):
            return ('B', 1000)
        if (objA - objB > ZEROISH_OBJ_THRESH) and (scA - scB > ZEROISH_SC_THRESH):
            return ('A', 1000)
        if objA >= objB:
            return ('A', 0 if (objA - objB) <= ZEROISH_OBJ_THRESH else 1000)
        else:
            return ('B', 0 if (objB - objA) <= ZEROISH_OBJ_THRESH else 1000)

    # microish: TB4 유지
    if microish_opp:
        opp_guess = 600 + 1500*contest_rate + 900*opp_aggr
        if non_got_cnt >= 3:   opp_guess += 400
        elif non_got_cnt >= 2: opp_guess += 250
        opp_guess = max(400, min(2600, opp_guess))

        diff_obj = objA - objB
        diff_sc  = scA - scB

        if (diff_obj > MICROISH_OBJ_THRESH) and (diff_sc > MICROISH_SC_THRESH):
            want = 'A'
        elif (-diff_obj > MICROISH_OBJ_THRESH) and (-diff_sc > MICROISH_SC_THRESH):
            want = 'B'
        else:
            if non_got_cnt >= 2:
                if diff_obj > 500:  return ('A', 1000)
                if -diff_obj > 500: return ('B', 1000)
            if diff_obj > 300:  return ('A', 750)
            if -diff_obj > 300: return ('B', 750)
            return ('A' if diff_obj >= 0 else 'B', 0)

        bid = 0
        for step in MICROISH_STEPS:
            if step > opp_guess:
                bid = step; break
        if non_got_cnt >= 3 and bid < 1750:
            bid = 1750
        return (want, bid)

    # ==== aggrish(#7 대응): EV 예측을 쓰되, 캡 완화, next-bucket 초과 확정 ====
    if aggrish_opp:
        # 기본 EV 예측 요소 계산
        rA_opp, sA_opp = best_rule_and_score_exact(A, available_rules, 0)
        rB_opp, sB_opp = best_rule_and_score_exact(B, available_rules, 0)
        dOpp = abs(sA_opp - sB_opp)
        opp_pref = 'A' if sA_opp >= sB_opp else 'B'
        threatened_rule = rA_opp if opp_pref == 'A' else rB_opp

        # anchor & 캡 완화(최대 5k)
        anchor = 0.5 * dOpp
        if threatened_rule == DiceRule.YACHT:           anchor += 2500
        elif threatened_rule == DiceRule.LARGE_STRAIGHT:anchor += 1500
        elif threatened_rule == DiceRule.FOUR_OF_A_KIND:anchor += 750
        if rounds_left <= 3: anchor *= 1.10
        opp_b = nearest_bucket(anchor, BID_BUCKETS)

        # 캡: 공격적이면 4000~5000 허용
        cap = 5000 if (opp_aggr >= 0.75 or contest_rate >= 0.75 or threat_score(threatened_rule) >= 2) else 4000
        opp_b = min(opp_b, cap)

        # 본인인 우위/위협 판정
        diff_obj = objA - objB
        diff_sc  = scA - scB
        strongA = (diff_obj > AGGRISH_STRONG_OBJ and diff_sc > AGGRISH_STRONG_SC)
        strongB = (-diff_obj > AGGRISH_STRONG_OBJ and -diff_sc > AGGRISH_STRONG_SC)

        if strongA or strongB or is_threat_rule(threatened_rule):
            want = 'A' if (strongA or (not strongB and diff_obj >= 0)) else 'B'
            base = next_bucket_above(opp_b, BID_BUCKETS)  # '살짝 상회'
            # 연속 미획득/후반 압박 시 한 단계 더
            if non_got_cnt >= 3 or rounds_left <= 5:
                base = next_bucket_above(base, BID_BUCKETS)
            # 너무 낮게 깔리면 2500 이상 보정
            base = max(base, 2500 if (strongA or strongB) else 1750)
            return (want, base)
        # 강우위/위협 아니면 EV 경로로 계속 ↓ (아래 공통 EV)

    # ==== 공통 EV 경로 ====
    rA, sA = best_rule_and_score_exact(A, available_rules, upper_progress)
    rB, sB = best_rule_and_score_exact(B, available_rules, upper_progress)
    rA_opp, sA_opp = best_rule_and_score_exact(A, available_rules, 0)
    rB_opp, sB_opp = best_rule_and_score_exact(B, available_rules, 0)

    dOpp = abs(sA_opp - sB_opp)
    opp_pref = 'A' if sA_opp >= sB_opp else 'B'
    q_high = max(0.55, min(0.85, 0.55 + 0.30 * (1.0 - pow(2.71828, -dOpp / 8000.0))))
    q_low  = 0.08

    threatened_rule = rA_opp if opp_pref == 'A' else rB_opp

    early = (round_no <= 2)
    mid_early = (round_no <= 4)

    anchor = 0.5 * dOpp
    if threatened_rule == DiceRule.YACHT:
        anchor += 2500
    elif threatened_rule == DiceRule.LARGE_STRAIGHT:
        anchor += 1500
    elif threatened_rule == DiceRule.FOUR_OF_A_KIND:
        anchor += 750
    if rounds_left <= 3:
        anchor *= 1.10

    candidate_buckets = list(BID_BUCKETS)
    if round_no == 1:
        candidate_buckets = [b for b in candidate_buckets if b in BID_BUCKETS_R1]

    if early:
        opp_b = 0
        candidate_buckets = [0, 1000, 1750]
        if threatened_rule == DiceRule.YACHT and dOpp >= 10000:
            candidate_buckets = [0, 1000, 1750, 2500, 3500]
    else:
        opp_b = nearest_bucket(anchor, candidate_buckets)
        if mid_early and threat_score(threatened_rule) <= 1:
            opp_b = min(opp_b, 1750)

    if opp_aggr > 0 and not early:
        scale = 1.0 + 0.8 * max(0.0, min(1.0, opp_aggr))
        opp_b = nearest_bucket(opp_b * scale, candidate_buckets)

    # 전역 캡(완화): 공격/연속미획득이면 2500~3500까지 허용
    if threat_score(threatened_rule) < 3 and dOpp < 7000:
        cap = 3500 if (opp_aggr >= 0.75 or non_got_cnt >= 4) else (2500 if (opp_aggr >= 0.6 or non_got_cnt >= 3) else 1250)
        opp_b = min(opp_b, cap)

    best = None
    for choice in ('A', 'B'):
        u_des = sA if choice == 'A' else sB
        u_alt = sB if choice == 'A' else sA
        q = q_high if choice == opp_pref else q_low
        for b in candidate_buckets:
            ev_raw = ev_resolve(u_des, u_alt, q, b, opp_b)
            ev_adj = ev_raw - BID_SOFT_COST * b
            cand = (ev_adj, choice, b, ev_raw)
            if best is None or ev_adj > best[0] + 1e-9:
                best = cand
            else:
                if abs(ev_adj - best[0]) <= TIE_DELTA:
                    dS = abs(u_des - u_alt)
                    if (b < best[2]) or (dS >= HIGH_DIFF_PUSH and b > best[2]):
                        best = cand

    # 최소 승리 다운시프트
    if best is not None:
        ev_adj_best, ch_best, b_best, _ = best
        sorted_b = sorted(set(candidate_buckets))
        min_win = next((b for b in sorted_b if b > opp_b), None)
        if (min_win is not None) and (min_win < b_best):
            u_des = sA if ch_best == 'A' else sB
            u_alt = sB if ch_best == 'A' else sA
            q = q_high if ch_best == opp_pref else q_low
            ev_raw2 = ev_resolve(u_des, u_alt, q, min_win, opp_b)
            ev_adj2 = ev_raw2 - BID_SOFT_COST * min_win
            if ev_adj2 >= ev_adj_best - 1200:
                best = (ev_adj2, ch_best, min_win, ev_raw2)

    if best is None:
        return ('A', 0)
    _, choice, bid, _ = best
    return (choice, bid)

# ===== 데이터 모델 + 게임 로직 =====
@dataclass
class Bid:
    group: str
    amount: int

@dataclass
class DicePut:
    rule: DiceRule
    dice: List[int]

class Bot:
    def __init__(self):
        self.round = 1
        self.my_side: Optional[str] = None
        self.got_my_get_this_round = False
        self.last_A: List[int] = [0]*5
        self.last_B: List[int] = [0]*5
        self.my_carry: List[int] = []
        self.my_taken_this_round: List[int] = []
        self.rule_score: List[Optional[int]] = [None]*12
        self.bid_score_my = 0
        self.last_my_bid = Bid('A', 0)
        self.opp_aggr = 0.0
        self.non_got_cnt = 0
        self.bid_rounds_cnt = 0

    def available_rules(self) -> List[DiceRule]:
        return [DiceRule(i) for i, v in enumerate(self.rule_score) if v is None]

    def upper_progress(self) -> int:
        return sum(v for i, v in enumerate(self.rule_score) if v is not None and i < 6)

    def my_upper_filled(self) -> int:
        return sum(1 for i in range(6) if self.rule_score[i] is not None)

    def total_score(self) -> int:
        upper = sum(v for i, v in enumerate(self.rule_score) if v is not None and i < 6)
        combo = sum(v for i, v in enumerate(self.rule_score) if v is not None and i >= 6)
        bonus = 35000 if upper >= 63000 else 0
        return upper + combo + bonus + self.bid_score_my

    def calc_bid(self, A: List[int], B: List[int]) -> Bid:
        self.bid_rounds_cnt += 1
        g, amt = choose_bid(
            A=A, B=B, my_carry=self.my_carry,
            available_rules=self.available_rules(),
            round_no=self.round,
            upper_progress=self.upper_progress(),
            rounds_left=max(0, 13 - self.round),
            opp_aggr=self.opp_aggr,
            non_got_cnt=self.non_got_cnt,
            bid_rounds_cnt=self.bid_rounds_cnt
        )
        return Bid(g, int(amt))

    def on_get_with_side(self, side_token: str, group_token: str):
        if self.my_side is None:
            self.my_side = side_token
        if side_token != self.my_side or self.got_my_get_this_round:
            return
        taken = self.last_A if group_token == 'A' else self.last_B
        self.my_taken_this_round = list(taken)
        self.got_my_get_this_round = True

        got_desired = (self.last_my_bid.group == group_token)
        self.bid_score_my += (-self.last_my_bid.amount if got_desired else self.last_my_bid.amount)
        self._update_opp_aggr(got_desired)
        if not got_desired:
            self.non_got_cnt += 1

        if self.round == 1:
            self.my_carry = list(self.my_taken_this_round)
            self.my_taken_this_round = []
            self.got_my_get_this_round = False
            self.round = 2

    def on_get_basic(self, got_group: str, _opp_group: str, _opp_score: int):
        if self.got_my_get_this_round:
            return
        self.my_taken_this_round = list(self.last_A if got_group == 'A' else self.last_B)
        self.got_my_get_this_round = True

        got_desired = (self.last_my_bid.group == got_group)
        self.bid_score_my += (-self.last_my_bid.amount if got_desired else self.last_my_bid.amount)
        self._update_opp_aggr(got_desired)
        if not got_desired:
            self.non_got_cnt += 1

        if self.round == 1:
            self.my_carry = list(self.my_taken_this_round)
            self.my_taken_this_round = []
            self.got_my_get_this_round = False
            self.round = 2

    def _update_opp_aggr(self, got_desired: bool):
        b = self.last_my_bid.amount
        if b == 0 and not got_desired:
            self.opp_aggr = min(1.0, self.opp_aggr + 0.35)
        elif b > 0 and not got_desired:
            self.opp_aggr = min(1.0, self.opp_aggr + 0.22)
        elif b > 0 and got_desired:
            self.opp_aggr = max(0.0, self.opp_aggr - 0.10)
        else:  # b == 0 and got_desired
            self.opp_aggr = max(0.0, self.opp_aggr - 0.06)

    def on_score(self) -> 'DicePut':
        if self.round == 13:
            hand = list(self.my_carry)
            if len(hand) != 5:
                hand = sorted(hand, reverse=True)[:5]
            avail = self.available_rules()
            best_rule, best_sc, best_pref = None, -1, -1
            for r in avail:
                sc = score_by_rule(hand, r)
                pref = 2 if r in UPPER else (1 if r == DiceRule.CHOICE else 0)
                if (sc > best_sc) or (sc == best_sc and pref > best_pref):
                    best_sc, best_rule, best_pref = sc, r, pref
            if best_rule is None:
                best_rule = DiceRule.CHOICE if DiceRule.CHOICE in avail else avail[0]
            put = DicePut(best_rule, list(hand))
            self._commit_put(hand, put)
            return put

        hand10 = list(self.my_carry) + list(self.my_taken_this_round)
        if len(hand10) < 5:
            dice5 = sorted(hand10, reverse=True)[:5]
            avail = self.available_rules()
            rule = DiceRule.CHOICE if DiceRule.CHOICE in avail else (avail[0] if avail else DiceRule.CHOICE)
            put = DicePut(rule, dice5)
            self._commit_put(hand10, put)
            return put

        avail = self.available_rules()
        rule, dice5 = best_put_with_stash(
            hand10=hand10,
            available_rules=avail,
            rounds_left=max(0, 13 - self.round),
            upper_progress=self.upper_progress()
        )

        if not multiset_ok(hand10, dice5):
            if len(self.my_taken_this_round) >= 5:
                dice5 = list(self.my_taken_this_round)[:5]
                rule = DiceRule.CHOICE if DiceRule.CHOICE in avail else (avail[0] if avail else DiceRule.CHOICE)
            else:
                dice5 = sorted(hand10, reverse=True)[:5]
                rule = DiceRule.CHOICE if DiceRule.CHOICE in avail else (avail[0] if avail else DiceRule.CHOICE)

        put = DicePut(rule, dice5)
        self._commit_put(hand10, put)
        return put

    def _commit_put(self, hand_snapshot: List[int], put: 'DicePut'):
        self.rule_score[put.rule.value] = score_by_rule(put.dice, put.rule)
        tmp = list(hand_snapshot)
        for v in put.dice:
            tmp.remove(v)
        self.my_carry = list(tmp)
        self.my_taken_this_round = []
        self.got_my_get_this_round = False
        self.round += 1

# ===== 메인 루프 =====
def main():
    random.seed(42)
    bot = Bot()

    def _clamp_die(v: int) -> int:
        return 1 if v < 1 else (6 if v > 6 else v)

    while True:
        try:
            line = sys.stdin.readline()
            if not line:
                break
            line = line.strip()
            if not line:
                continue

            parts = line.split()
            cmd = parts[0].upper()

            if cmd == "READY":
                say("OK")

            elif cmd == "ROLL":
                if len(parts) >= 3 and len(parts[1]) == 5 and len(parts[2]) == 5:
                    A = [_clamp_die(int(c)) for c in parts[1]]
                    B = [_clamp_die(int(c)) for c in parts[2]]
                    bot.last_A, bot.last_B = A, B
                    bid = bot.calc_bid(A, B)
                    bot.last_my_bid = bid
                    say(f"BID {bid.group} {bid.amount}")
                else:
                    say("BID A 0")

            elif cmd == "GET":
                if len(parts) == 3 and parts[1].upper() in ("FIRST","SECOND"):
                    bot.on_get_with_side(parts[1].upper(), parts[2].upper())
                elif len(parts) >= 4:
                    got = parts[1].upper()
                    opp_g = parts[2].upper()
                    try:
                        opp_x = int(parts[3])
                    except:
                        opp_x = 0
                    bot.on_get_basic(got, opp_g, opp_x)

            elif cmd == "SCORE":
                put = bot.on_score()
                dice_str = "".join(map(str, sorted(put.dice, reverse=True)))
                say(f"PUT {put.rule.name} {dice_str}")

            elif cmd == "SET":
                pass

            elif cmd == "FINISH":
                break

        except Exception:
            try:
                hand = list(bot.my_carry) + list(bot.my_taken_this_round)
                use5 = sorted(hand, reverse=True)[:5]
                if len(use5) == 5:
                    say("PUT CHOICE " + "".join(map(str, sorted(use5, reverse=True))))
                else:
                    say("FINISH")
            except Exception:
                say("FINISH")
            break

if __name__ == "__main__":
    main()
