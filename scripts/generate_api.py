#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Authors: Formal Frontier Agents
"""Bounded native doc-gen4 Markdown/JSON adapter for continuous group cohomology.

Adapted from Formal Frontier's profinite-groups and finite-group Tate adapters,
with earlier documentation patterns from polynomial-root-stability and
ideal-completion. This validates documentation inputs, not proofs or releases.
"""

if not __debug__:
    raise SystemExit("optimized Python is not supported for API generation")

import argparse
import hashlib
from html.parser import HTMLParser
import json
from pathlib import Path
import re


TOOL = "97d4ecdfc8e09e7f511724c25e303d448de6a3db"
TOOL_TREE = "ebf77f3e174c145c9ca2db0df1c18a78ae87c93b"
SOURCE = "afd0296d5138cc87f365aebe1d6d6d33c5546ba9"
SOURCE_TREE = "cfb84abe6f06142f5c898f22a5a2fe9760fbc6a6"
RAW_ORIGIN = "f73154dfa181cc8fd00a102c58f221940a335ad0"
PUBLISHED_SOURCE = "be74358d7b1140e76ab6b2ad72f6aa068138e687"
PUBLISHED_SOURCE_REPOSITORY = "https://github.com/FormalFrontier/continuous-group-cohomology"
PUBLISHED_SOURCE_URL = PUBLISHED_SOURCE_REPOSITORY + "/blob/" + PUBLISHED_SOURCE
LINE_OFFSETS = {
    "ContinuousGroupCohomology.NestedInvariants": 4,
    "ContinuousGroupCohomology.TopModuleCatUlift": 4,
}
PRODUCTION = (
    "ContinuousGroupCohomology",
    "ContinuousGroupCohomology.ClosedTopologicalCoinvariants",
    "ContinuousGroupCohomology.CompactAddCommGroup",
    "ContinuousGroupCohomology.CompactAddCommGroupLimits",
    "ContinuousGroupCohomology.CompactFiniteHomology",
    "ContinuousGroupCohomology.CompactTopModuleLimits",
    "ContinuousGroupCohomology.Composition",
    "ContinuousGroupCohomology.ContinuousCohomologyUlift",
    "ContinuousGroupCohomology.ContinuousGroupExtension",
    "ContinuousGroupCohomology.Corestriction",
    "ContinuousGroupCohomology.DegreeOne",
    "ContinuousGroupCohomology.FiniteCoinvariants",
    "ContinuousGroupCohomology.FiniteNegativeDeflation",
    "ContinuousGroupCohomology.GroupExtensionUlift",
    "ContinuousGroupCohomology.HomogeneousCochainsUlift",
    "ContinuousGroupCohomology.LevelCompact",
    "ContinuousGroupCohomology.LevelCompactFunctoriality",
    "ContinuousGroupCohomology.LevelCompactNorm",
    "ContinuousGroupCohomology.LowDegreeExact",
    "ContinuousGroupCohomology.Mackey",
    "ContinuousGroupCohomology.NestedInvariants",
    "ContinuousGroupCohomology.NormalizedCohomology",
    "ContinuousGroupCohomology.QuotientConjugationAction",
    "ContinuousGroupCohomology.RestrictedLevelCompact",
    "ContinuousGroupCohomology.TopModuleCatUlift",
    "ContinuousGroupCohomology.TopRepUlift",
    "ContinuousGroupCohomology.TopologicalModN",
    "ContinuousGroupCohomology.TopologicalQuotientConjugationAction",
)
CLIENTS = (
    "examples.CompactFoundationNative",
    "examples.FiniteCoinvariantsNative",
    "examples.FiniteNegativeNative",
    "examples.LevelCompactNative",
    "examples.LevelCompactNormNative",
    "examples.NativeCore",
    "examples.NestedInvariantsNative",
    "examples.RestrictedLevelNative",
)
MODULES = PRODUCTION + CLIENTS
KINDS = ("def", "theorem", "instance", "structure", "class", "ctor")

# Filled from the frozen source bytes and independently extracted native records.
SOURCE_INPUT_SHA256 = {
    'ContinuousGroupCohomology/ClosedTopologicalCoinvariants.lean': 'e184aa75d7163a81f5f4f43b3f2393741c20cf9a379e84371b1a64dfcdef5661',
    'ContinuousGroupCohomology/CompactAddCommGroup.lean': 'acd9b89d6279f9d39731305bfa42da87d0eedc7764c08b2c32decdd6a20ae838',
    'ContinuousGroupCohomology/CompactAddCommGroupLimits.lean': '96c5e07d5a8721a28497a995186d4fb9b0e591633645312e71cb4b18d59d47a8',
    'ContinuousGroupCohomology/CompactFiniteHomology.lean': '84bf792e94e3df1887029b6f5cc46eacbf52fd25e20122508a63e0b72eb06a06',
    'ContinuousGroupCohomology/CompactTopModuleLimits.lean': '693ef6f28a708bac1c9238b6b615490bc45f75624b708c2f60b0711c221479ee',
    'ContinuousGroupCohomology/Composition.lean': 'dd46a55160d5355a4a972a4eda5996aa677088a212d73d2b7f821c39016b1063',
    'ContinuousGroupCohomology/ContinuousCohomologyUlift.lean': 'f1c68ed88b59903491f357a42374f9da1f73b88b892390a9ced8b175125dd00d',
    'ContinuousGroupCohomology/ContinuousGroupExtension.lean': '23efce5f6f02231c384b07749afcd7bd4847d0f13d15fc4b3c4e7a64f9b8976b',
    'ContinuousGroupCohomology/Corestriction.lean': '89fbe92b7def9bb54a027a2ec571c379d15af454a528e7e4a3b5b55203f5ce86',
    'ContinuousGroupCohomology/DegreeOne.lean': '604fe23e8de358ada687b91f2e18da25df8244f69bd5681f1c0db73365b6d2fb',
    'ContinuousGroupCohomology/FiniteCoinvariants.lean': '9ac5a0289d089cf85e5d79a6a1c8dc0d0509a9481f101581093f04392eba18a4',
    'ContinuousGroupCohomology/FiniteNegativeDeflation.lean': '5a1637762b33c1cf76a1b4d905f78d831b69fab184556233c1517c24a45e0a0f',
    'ContinuousGroupCohomology/GroupExtensionUlift.lean': 'cd6b7d8bce9a7f912acaabedda2a462d5cb0440934ae283aaec620e8f6f159ed',
    'ContinuousGroupCohomology/HomogeneousCochainsUlift.lean': '7686107a60e1c46d6c84ef54cd7ac2e83ef760758227d43042547582a8266a60',
    'ContinuousGroupCohomology/LevelCompact.lean': 'e00e1c0bd633c941fc53b7d8c770bde745c7dc0f415056793ac79fe4f408766d',
    'ContinuousGroupCohomology/LevelCompactFunctoriality.lean': 'd8f5f80b2633828db5395b6add02e7c79971fb9fe9034588a9ed60e9e99566d9',
    'ContinuousGroupCohomology/LevelCompactNorm.lean': '5b9b435922506e8eed1675e3c881b4d47e3f1653e58dd0b9e91eba97dff16f16',
    'ContinuousGroupCohomology/LowDegreeExact.lean': '434a58b3a2f1a6413abbe2dad156b84a7ed1a532b7ab9668421a0dbdb644765c',
    'ContinuousGroupCohomology/Mackey.lean': 'fe5116eacbf4f4272ae5b8ffc48fa09372c169296d266363843db6274303043c',
    'ContinuousGroupCohomology/NestedInvariants.lean': 'f3a5cdd3dbc7ce276c3c5c2a73271e3bd1445cb9f1d4ade57fa9a5fcbccc4f13',
    'ContinuousGroupCohomology/NormalizedCohomology.lean': '8d3b4697bd72fa2841c94e9dbe23dbedb70468c0fd338ed944364e2703865f53',
    'ContinuousGroupCohomology/QuotientConjugationAction.lean': '813653a059bc9ac75a58df514839b639b50f52482a153f77863bd1e11375b759',
    'ContinuousGroupCohomology/RestrictedLevelCompact.lean': 'be3d724cd7c0e2fbfeea7f1adfc2ed01dd88e33092bc754d8dcbe3d662e0f9d6',
    'ContinuousGroupCohomology/TopModuleCatUlift.lean': '31d5dc2b87ddd807ba6b28130c5fa09042fe992bb1a184bc78499d93d9543538',
    'ContinuousGroupCohomology/TopRepUlift.lean': 'c44c36e08e6ebdc5be0a4e87fc4e2e5e9466557989233f2d11b7151c86fac046',
    'ContinuousGroupCohomology/TopologicalModN.lean': '3a74b66188c74f391916db774f4c1add16b9fa5f806a523d0a0eba0f90cbc205',
    'ContinuousGroupCohomology/TopologicalQuotientConjugationAction.lean': '347b9ec0c5a42ca1a733eecff2668c0d2cce31d6fe69074ae983629a7b53cb80',
    'ContinuousGroupCohomology.lean': '1620d60e7eae37c5160ae3861954fe38a709795ecfa4b4e477437bcd09504be8',
    'examples/CompactFoundationNative.lean': 'acc41473f6e3601d64152d51c9f6f672bef713563ce0ffc7fe9f2f422a6a305b',
    'examples/FiniteCoinvariantsNative.lean': 'd909eb83927f19083f0bbac84824dddfcd4b5b64547aae252775153923048e28',
    'examples/FiniteNegativeNative.lean': 'cf7008e6d9c259cb74dd9b6343ea362b6bb286f40acd3a7369addd6e91df10f7',
    'examples/LevelCompactNative.lean': '0f5c5db15de8ebd52a0b21e8e0a4aedd62d3a42c303a6c99904c777753f960b5',
    'examples/LevelCompactNormNative.lean': '9b41453654acb5ec45c30cd4fc960350c24b7068a63942a27b1c1413c2491a72',
    'examples/NativeCore.lean': '78850ea3e011c19a485d6615c2f593d9001fc5d638a54676b4eefac82710a6f3',
    'examples/NestedInvariantsNative.lean': 'ce9984a16339c1a6238990cc21cb77ef8cb78cddd34862fc40ae9128b9e38ed1',
    'examples/RestrictedLevelNative.lean': 'bbbca81eee9044829c65a46ed83d42d1927bf9309bbeef525ea610e8c69da793',
    'lake-manifest.json': '303448a0c3fe4d37c8d189d0ec08348ee6cd6d696550b30b5e0c2f6c9ad1b04c',
    'lakefile.lean': '1b2b645b6ec8a77da9d31d3415f984dd02332032610c07b0bbaef1d67d75e05d',
    'lean-toolchain': '8190e75a201741065fe508b28955dd64dd72d090babe5f70ce6848879d68ae88',
}
NATIVE_RECORD_SHA256 = {
    'ContinuousGroupCohomology': 'b0cfa169f1aeb8beb5907e562852ad8457984a69b52f24dccf13450835bc07aa',
    'ContinuousGroupCohomology.ClosedTopologicalCoinvariants': 'bec558eba26d0da28c59dbbd444c1d6f3fb3dba0e3963ab6eefdc6ba6a10744c',
    'ContinuousGroupCohomology.CompactAddCommGroup': '86e17b51862713d438064fe30465e49774893ab492ca660018bd4bbd7a0ab34d',
    'ContinuousGroupCohomology.CompactAddCommGroupLimits': 'd1fe66af5d36ec5e238a82afd1d849164af073df70e5e8af9021f483991526b0',
    'ContinuousGroupCohomology.CompactFiniteHomology': '3865fe9327d760bd5bf7737b4af37b515bdfa33761e5118d04f23e8f70ec5678',
    'ContinuousGroupCohomology.CompactTopModuleLimits': '301e06847fd542b94132efc55265e039fe47976a0d609bcb019e008bbe692623',
    'ContinuousGroupCohomology.Composition': 'a927a620218dc567eb4c7bd815adec4175a6da9c3306873b0a54e8f2070c8b88',
    'ContinuousGroupCohomology.ContinuousCohomologyUlift': '7918bc7c39acecdc41445d61572d1e3b0ddeb244ec2cc996f2acc3d3c3696727',
    'ContinuousGroupCohomology.ContinuousGroupExtension': '63a19c24e379a99f5b8e9c6a85118fc987c59d7ef6f8283bb87c4002331cbc72',
    'ContinuousGroupCohomology.Corestriction': '5777aade235b507c0bcd3dbbaf192ae9701ee53765385c3615ed162c8616d9cb',
    'ContinuousGroupCohomology.DegreeOne': '0eb557e857c07a1f5e353beb72d9d648080b641a7c1b60833756f290bb54aa77',
    'ContinuousGroupCohomology.FiniteCoinvariants': '713becc2c644abb22712ce88eaa0c453e0a171839b2aea75b96c4cca060bf473',
    'ContinuousGroupCohomology.FiniteNegativeDeflation': '13bdda893f3cac0e6b36413ea77636777518b9cc47a9e4298c396614c54cf1d2',
    'ContinuousGroupCohomology.GroupExtensionUlift': '7b62e929475055e24345d6d5a06de3d2ae7b4b52b37597d63ccee62af5d9d24c',
    'ContinuousGroupCohomology.HomogeneousCochainsUlift': '35577ce56c6372bd200d1203107cdc2c1faf323d80580fdf394888e6398ca2bf',
    'ContinuousGroupCohomology.LevelCompact': '7c07167f4031c88be9915fc652546a0c9656fe563e171d23a8b90926b1b889be',
    'ContinuousGroupCohomology.LevelCompactFunctoriality': 'bab23b33b7815c8ccb27c59f9220425e178c3632ac157fa16761ac4ee8fa9556',
    'ContinuousGroupCohomology.LevelCompactNorm': 'f8aa5e16671d02c4f8df967000c5fdaa552b00eebd7c20d707383ba619c74e5e',
    'ContinuousGroupCohomology.LowDegreeExact': '4246d4ed92d1b1e5a8494c1b32a45f3d37060e031e138d4d9599fa8219efb890',
    'ContinuousGroupCohomology.Mackey': 'a86c6a81ce59f883ef80d07ec40e3f595827e8ddac1b0167e235f1175106afc8',
    'ContinuousGroupCohomology.NestedInvariants': '29b991f5eb38789f98da1fd027558462f43f5b9fb15a71b9e273df0d566a1c78',
    'ContinuousGroupCohomology.NormalizedCohomology': 'd49bcc70c3297facf61a4e1033ef0881b1c5e5648b77b0d2145103107cd261cf',
    'ContinuousGroupCohomology.QuotientConjugationAction': '01f698cf6b41c8dd8eacd45a1fcc4fd89171eae52e68fd61c850d31148d46b79',
    'ContinuousGroupCohomology.RestrictedLevelCompact': 'f71f0c624de451a844340d6634415069c8e095c166f8d9832a29cf7f9d9dddcd',
    'ContinuousGroupCohomology.TopModuleCatUlift': '94b688a63e02c25eb6dea717fbb5345ca2d5cb39c90c1939cee5428a7dca7344',
    'ContinuousGroupCohomology.TopRepUlift': '9565cb6d68ef524d802aafe6ca0d1ec5b23ab1ebdfd17ff6ea8b3aeb03cb66f6',
    'ContinuousGroupCohomology.TopologicalModN': '7356e07edb933eefed4ab0e6d31a82e35be81b7092ca4d7d5e4490429351aecd',
    'ContinuousGroupCohomology.TopologicalQuotientConjugationAction': '676b88c7426e8bc7051f0fb92787e5a1aed4a15b493c65b3517d264e20089dd9',
    'examples.CompactFoundationNative': '6fb0f1284a8571057e957076c23aa2d3d1408500d41dc6f409bb263b9b11e69b',
    'examples.FiniteCoinvariantsNative': '75e7f3394da5437784c2c162ea0e2d744da13ebcf6d8ec1448f06eb1e684c8d1',
    'examples.FiniteNegativeNative': 'b7eb0e0735930c973a54cf3140a158b34188f80be445c797a504525a5cd5ed7b',
    'examples.LevelCompactNative': '9e7e571f2bc4f175e6dd7086cfa464d1d84d1ad41e6f75bf22df0b123534c81b',
    'examples.LevelCompactNormNative': '64b1246adbce5c18791961838df248b4057a92d900f0027f472961fa6bd53bfd',
    'examples.NativeCore': 'c3f15b8b3eb1bcb5f29e52b9422118eea7e482f000639f24086edcb45507ad83',
    'examples.NestedInvariantsNative': 'ebf32d68b8a10562f2517a1fa9f855525671c541dc89f98217e8b3d4ffdc3ee3',
    'examples.RestrictedLevelNative': '90294adc322958b22c2ae6a964a7ab38497fc34fe5becacf3ded83aa0c28d582',
}
COUNTS = {
    'ContinuousGroupCohomology': 0,
    'ContinuousGroupCohomology.ClosedTopologicalCoinvariants': 64,
    'ContinuousGroupCohomology.CompactAddCommGroup': 41,
    'ContinuousGroupCohomology.CompactAddCommGroupLimits': 13,
    'ContinuousGroupCohomology.CompactFiniteHomology': 10,
    'ContinuousGroupCohomology.CompactTopModuleLimits': 4,
    'ContinuousGroupCohomology.Composition': 38,
    'ContinuousGroupCohomology.ContinuousCohomologyUlift': 8,
    'ContinuousGroupCohomology.ContinuousGroupExtension': 31,
    'ContinuousGroupCohomology.Corestriction': 76,
    'ContinuousGroupCohomology.DegreeOne': 47,
    'ContinuousGroupCohomology.FiniteCoinvariants': 24,
    'ContinuousGroupCohomology.FiniteNegativeDeflation': 7,
    'ContinuousGroupCohomology.GroupExtensionUlift': 7,
    'ContinuousGroupCohomology.HomogeneousCochainsUlift': 13,
    'ContinuousGroupCohomology.LevelCompact': 18,
    'ContinuousGroupCohomology.LevelCompactFunctoriality': 20,
    'ContinuousGroupCohomology.LevelCompactNorm': 14,
    'ContinuousGroupCohomology.LowDegreeExact': 57,
    'ContinuousGroupCohomology.Mackey': 71,
    'ContinuousGroupCohomology.NestedInvariants': 9,
    'ContinuousGroupCohomology.NormalizedCohomology': 9,
    'ContinuousGroupCohomology.QuotientConjugationAction': 11,
    'ContinuousGroupCohomology.RestrictedLevelCompact': 29,
    'ContinuousGroupCohomology.TopModuleCatUlift': 18,
    'ContinuousGroupCohomology.TopRepUlift': 18,
    'ContinuousGroupCohomology.TopologicalModN': 66,
    'ContinuousGroupCohomology.TopologicalQuotientConjugationAction': 22,
    'examples.CompactFoundationNative': 0,
    'examples.FiniteCoinvariantsNative': 16,
    'examples.FiniteNegativeNative': 8,
    'examples.LevelCompactNative': 0,
    'examples.LevelCompactNormNative': 15,
    'examples.NativeCore': 5,
    'examples.NestedInvariantsNative': 0,
    'examples.RestrictedLevelNative': 25,
}
KIND_COUNTS = {
    'ContinuousGroupCohomology': {},
    'ContinuousGroupCohomology.ClosedTopologicalCoinvariants': {'theorem': 37, 'def': 22, 'instance': 3, 'ctor': 1, 'structure': 1},
    'ContinuousGroupCohomology.CompactAddCommGroup': {'theorem': 14, 'def': 16, 'instance': 7, 'ctor': 2, 'structure': 2},
    'ContinuousGroupCohomology.CompactAddCommGroupLimits': {'theorem': 6, 'instance': 4, 'def': 3},
    'ContinuousGroupCohomology.CompactFiniteHomology': {'theorem': 3, 'def': 7},
    'ContinuousGroupCohomology.CompactTopModuleLimits': {'theorem': 2, 'def': 2},
    'ContinuousGroupCohomology.Composition': {'theorem': 25, 'def': 12, 'instance': 1},
    'ContinuousGroupCohomology.ContinuousCohomologyUlift': {'theorem': 6, 'def': 2},
    'ContinuousGroupCohomology.ContinuousGroupExtension': {'theorem': 16, 'instance': 3, 'def': 8, 'ctor': 2, 'structure': 2},
    'ContinuousGroupCohomology.Corestriction': {'theorem': 51, 'instance': 4, 'def': 21},
    'ContinuousGroupCohomology.DegreeOne': {'theorem': 25, 'def': 22},
    'ContinuousGroupCohomology.FiniteCoinvariants': {'theorem': 12, 'def': 12},
    'ContinuousGroupCohomology.FiniteNegativeDeflation': {'theorem': 4, 'def': 3},
    'ContinuousGroupCohomology.GroupExtensionUlift': {'theorem': 5, 'def': 2},
    'ContinuousGroupCohomology.HomogeneousCochainsUlift': {'theorem': 5, 'def': 8},
    'ContinuousGroupCohomology.LevelCompact': {'theorem': 12, 'def': 4, 'ctor': 1, 'structure': 1},
    'ContinuousGroupCohomology.LevelCompactFunctoriality': {'theorem': 7, 'def': 7, 'instance': 2, 'ctor': 2, 'structure': 2},
    'ContinuousGroupCohomology.LevelCompactNorm': {'theorem': 10, 'def': 4},
    'ContinuousGroupCohomology.LowDegreeExact': {'theorem': 37, 'def': 16, 'ctor': 2, 'structure': 2},
    'ContinuousGroupCohomology.Mackey': {'theorem': 42, 'def': 27, 'instance': 2},
    'ContinuousGroupCohomology.NestedInvariants': {'theorem': 6, 'def': 3},
    'ContinuousGroupCohomology.NormalizedCohomology': {'theorem': 3, 'def': 6},
    'ContinuousGroupCohomology.QuotientConjugationAction': {'theorem': 9, 'def': 2},
    'ContinuousGroupCohomology.RestrictedLevelCompact': {'theorem': 14, 'def': 13, 'ctor': 1, 'structure': 1},
    'ContinuousGroupCohomology.TopModuleCatUlift': {'instance': 8, 'def': 4, 'theorem': 6},
    'ContinuousGroupCohomology.TopRepUlift': {'instance': 3, 'theorem': 9, 'def': 4, 'ctor': 1, 'class': 1},
    'ContinuousGroupCohomology.TopologicalModN': {'def': 23, 'theorem': 36, 'instance': 7},
    'ContinuousGroupCohomology.TopologicalQuotientConjugationAction': {'theorem': 15, 'def': 7},
    'examples.CompactFoundationNative': {},
    'examples.FiniteCoinvariantsNative': {'theorem': 14, 'def': 2},
    'examples.FiniteNegativeNative': {'theorem': 7, 'def': 1},
    'examples.LevelCompactNative': {},
    'examples.LevelCompactNormNative': {'theorem': 12, 'def': 3},
    'examples.NativeCore': {'theorem': 5},
    'examples.NestedInvariantsNative': {},
    'examples.RestrictedLevelNative': {'theorem': 19, 'def': 6},
}
EXPECTED_INSTANCES = {
    'ContinuousGroupCohomology.ClosedTopologicalCoinvariants': {'PointwiseContinuousMulAction.instCoeFun': ('CoeFun', ('PointwiseContinuousMulAction',)), 'PointwiseContinuousMulAction.instNormalDifferenceSubgroup': ('Subgroup.Normal', ('PointwiseContinuousMulAction.differenceSubgroup',)), 'PointwiseContinuousMulAction.instNormalClosedDifferenceSubgroup': ('Subgroup.Normal', ('PointwiseContinuousMulAction.closedDifferenceSubgroup',))},
    'ContinuousGroupCohomology.CompactAddCommGroup': {'instCoeSortCompHausAddCommGrpType': ('CoeSort', ('CompHausAddCommGrp', '_builtin_typeu')), 'CompHausAddCommGrp.instCategory': ('CategoryTheory.Category', ('CompHausAddCommGrp',)), 'CompHausAddCommGrp.instConcreteCategoryContinuousAddMonoidHomCarrierToTopTrueToCompHaus': ('CategoryTheory.ConcreteCategory', ('CompHausAddCommGrp',)), 'CompHausAddCommGrp.instCoeFunHomForallCarrierToTopTrueToCompHaus': ('CoeFun', ('Quiver.Hom',)), 'CompHausAddCommGrp.instHasForget₂ContinuousAddMonoidHomCarrierToTopTrueToCompHausCompHausContinuousMap': ('CategoryTheory.HasForget₂', ('CompHausAddCommGrp', 'CompHaus')), 'CompHausAddCommGrp.instFaithfulCompHausForget₂ContinuousAddMonoidHomCarrierToTopTrueToCompHausContinuousMap': ('CategoryTheory.Functor.Faithful', ('CategoryTheory.forget₂',)), 'CompHausAddCommGrp.instHasForget₂ContinuousAddMonoidHomCarrierToTopTrueToCompHausAddCommGrpCatAddMonoidHomCarrier': ('CategoryTheory.HasForget₂', ('CompHausAddCommGrp', 'AddCommGrpCat'))},
    'ContinuousGroupCohomology.CompactAddCommGroupLimits': {'CompHausAddCommGrp.instAddCommGroupCarrierToTopTruePtCompHausLimitConeCompForget₂ContinuousAddMonoidHomToCompHausContinuousMap': ('AddCommGroup', ('TopCat.carrier',)), 'CompHausAddCommGrp.instIsTopologicalAddGroupCarrierToTopTruePtCompHausLimitConeCompForget₂ContinuousAddMonoidHomToCompHausContinuousMap': ('IsTopologicalAddGroup', ('TopCat.carrier',)), 'CompHausAddCommGrp.instHasLimit': ('CategoryTheory.Limits.HasLimit', ()), 'CompHausAddCommGrp.instPreservesLimitCompHausForget₂ContinuousAddMonoidHomCarrierToTopTrueToCompHausContinuousMap': ('CategoryTheory.Limits.PreservesLimit', ('CategoryTheory.forget₂',))},
    'ContinuousGroupCohomology.Composition': {'OpenSubgroup.transFiniteIndex': ('Subgroup.FiniteIndex', ('OpenSubgroup.toSubgroup',))},
    'ContinuousGroupCohomology.ContinuousGroupExtension': {'ContinuousGroupExtension.Equiv.instEquivLike': ('EquivLike', ('ContinuousGroupExtension.Equiv',)), 'ContinuousGroupExtension.Equiv.instMulEquivClass': ('MulEquivClass', ('ContinuousGroupExtension.Equiv',)), 'ContinuousGroupExtension.Equiv.instHomeomorphClass': ('HomeomorphClass', ('ContinuousGroupExtension.Equiv',))},
    'ContinuousGroupCohomology.Corestriction': {'TopRep.jointlyContinuous_res': ('TopRep.JointlyContinuous', ('TopRep.res',)), 'ContinuousCohomology.CorestrictionTransversal.openSubgroupIsTopologicalGroup': ('IsTopologicalGroup', ('Subtype',)), 'ContinuousCohomology.CorestrictionTransversal.openSubgroupTopFiniteIndex': ('Subgroup.FiniteIndex', ('OpenSubgroup.toSubgroup',)), 'ContinuousCohomology.CorestrictionTransversal.openSubgroupTopLocallyCompact': ('LocallyCompactSpace', ('Subtype',))},
    'ContinuousGroupCohomology.LevelCompactFunctoriality': {'ContinuousGroupCohomology.LevelCompactRep.instCategory': ('CategoryTheory.Category', ('ContinuousGroupCohomology.LevelCompactRep',)), 'ContinuousGroupCohomology.LevelCompactRep.instFaithfulRepForget': ('CategoryTheory.Functor.Faithful', ('ContinuousGroupCohomology.LevelCompactRep.forget',))},
    'ContinuousGroupCohomology.Mackey': {'ContinuousCohomology.CorestrictionTransversal.mackeyOpenStabilizerFiniteIndex': ('Subgroup.FiniteIndex', ('OpenSubgroup.toSubgroup',)), 'ContinuousCohomology.CorestrictionTransversal.mackeyDoubleCosetFinite': ('Finite', ('DoubleCoset.Quotient',))},
    'ContinuousGroupCohomology.TopModuleCatUlift': {'ULift.instIsTopologicalAddGroupOfIsTopologicalAddGroup': ('IsTopologicalAddGroup', ('ULift',)), 'ULift.instContinuousSMulOfContinuousSMul': ('ContinuousSMul', ('ULift',)), 'TopModuleCat.instFullUliftFunctor': ('CategoryTheory.Functor.Full', ('TopModuleCat.uliftFunctor',)), 'TopModuleCat.instFaithfulUliftFunctor': ('CategoryTheory.Functor.Faithful', ('TopModuleCat.uliftFunctor',)), 'TopModuleCat.instAdditiveUliftFunctor': ('CategoryTheory.Functor.Additive', ('TopModuleCat.uliftFunctor',)), 'TopModuleCat.instEssSurjUliftFunctorSameUniverse': ('CategoryTheory.Functor.EssSurj', ('TopModuleCat.uliftFunctor',)), 'TopModuleCat.instIsEquivalenceUliftFunctorSameUniverse': ('CategoryTheory.Functor.IsEquivalence', ('TopModuleCat.uliftFunctor',)), 'TopModuleCat.instLinearUliftFunctor': ('CategoryTheory.Functor.Linear', ('TopModuleCat.uliftFunctor',))},
    'ContinuousGroupCohomology.TopRepUlift': {'TopRep.instAdditiveUliftFunctor': ('CategoryTheory.Functor.Additive', ('TopRep.uliftFunctor',)), 'TopRep.jointlyContinuousUlift': ('TopRep.JointlyContinuous', ('TopRep.ulift',)), 'TopRep.instLinearUliftFunctor': ('CategoryTheory.Functor.Linear', ('TopRep.uliftFunctor',))},
    'ContinuousGroupCohomology.TopologicalModN': {'TopologicalModN.instModule': ('Module', ('ZMod', 'TopologicalModN')), 'TopologicalModN.instContinuousSMul': ('ContinuousSMul', ('ZMod', 'TopologicalModN')), 'TopologicalModN.instT1Space': ('T1Space', ('TopologicalModN',)), 'TopologicalModN.instT2Space': ('T2Space', ('TopologicalModN',)), 'TopologicalModN.instTopologicalSpaceModN': ('TopologicalSpace', ('ModN',)), 'TopologicalPowerQuotient.instT1Space': ('T1Space', ('TopologicalPowerQuotient',)), 'TopologicalPowerQuotient.instT2Space': ('T2Space', ('TopologicalPowerQuotient',))},
}
DOC_LINK_OVERRIDES = {}
GENERATED_ANCHORS = {
    'CompHausAddCommGrp.Hom.ext_iff': (67, '@[ext]'),
    'CompHausAddCommGrp.Hom.mk': (66, '/-- Morphisms of compact Hausdorff topological additive commutative groups. -/'),
    'CompHausAddCommGrp.hom_ext_iff': (105, '@[ext]'),
    'CompHausAddCommGrp.instAddCommGroupCarrierToTopTruePtCompHausLimitConeCompForget₂ContinuousAddMonoidHomToCompHausContinuousMap': (49, 'instance : AddCommGroup'),
    'CompHausAddCommGrp.instCategory': (72, 'instance : Category CompHausAddCommGrp where'),
    'CompHausAddCommGrp.instCoeFunHomForallCarrierToTopTrueToCompHaus': (92, 'instance {A B : CompHausAddCommGrp.{u}} : CoeFun (A ⟶ B) (fun _ ↦ A → B) where'),
    'CompHausAddCommGrp.instConcreteCategoryContinuousAddMonoidHomCarrierToTopTrueToCompHaus': (77, 'instance : ConcreteCategory CompHausAddCommGrp (fun A B ↦ A →ₜ+ B) where'),
    'CompHausAddCommGrp.instFaithfulCompHausForget₂ContinuousAddMonoidHomCarrierToTopTrueToCompHausContinuousMap': (117, 'instance : (forget₂ CompHausAddCommGrp CompHaus).Faithful where'),
    'CompHausAddCommGrp.instHasForget₂ContinuousAddMonoidHomCarrierToTopTrueToCompHausAddCommGrpCatAddMonoidHomCarrier': (123, '/-- Forget to the underlying additive commutative group. -/'),
    'CompHausAddCommGrp.instHasForget₂ContinuousAddMonoidHomCarrierToTopTrueToCompHausCompHausContinuousMap': (110, '/-- Forget a compact Hausdorff topological additive commutative group to its'),
    'CompHausAddCommGrp.instHasLimit': (100, 'instance : HasLimit F where'),
    'CompHausAddCommGrp.instHasLimitsOfShape': (270, 'noncomputable local instance :'),
    'CompHausAddCommGrp.instIsTopologicalAddGroupCarrierToTopTruePtCompHausLimitConeCompForget₂ContinuousAddMonoidHomToCompHausContinuousMap': (53, 'instance : IsTopologicalAddGroup'),
    'CompHausAddCommGrp.instPreservesLimitCompHausForget₂ContinuousAddMonoidHomCarrierToTopTrueToCompHausContinuousMap': (103, 'instance : PreservesLimit F (forget₂ CompHausAddCommGrp CompHaus) :='),
    'CompHausAddCommGrp.mk': (34, '/-- The category of compact Hausdorff topological additive commutative groups. -/'),
    'ContinuousCohomology.CorestrictionTransversal.homologyQuotientIso_restrict_assoc': (822, '@[reassoc]'),
    'ContinuousCohomology.CorestrictionTransversal.homologyQuotientIso_trans_assoc': (487, '@[reassoc]'),
    'ContinuousCohomology.CorestrictionTransversal.transDegreeOne_eq_map': (540, 'lemma transDegreeOne_eq_map (H : OpenSubgroup G) (K : OpenSubgroup H)'),
    'ContinuousCohomology.CorestrictionTransversal.transferQuotient_comp_crossedQuotientRestrict_mackey_hom_assoc': (1429, '@[reassoc]'),
    'ContinuousCohomology.CorestrictionTransversal.transferQuotient_comp_restrict_hom_assoc': (967, '@[reassoc]'),
    'ContinuousCohomology.CorestrictionTransversal.transferQuotient_natural_hom_assoc': (644, '@[reassoc]'),
    'ContinuousCohomology.TopologicallySplitShortExact.Hom.mk': (104, '/-- A morphism of topologically split short exact sequences.  Compatibility'),
    'ContinuousCohomology.TopologicallySplitShortExact.mk': (30, '/-- A short exact sequence of topological representations equipped with'),
    'ContinuousCohomology.degreeOneIso_natural_assoc': (553, '@[reassoc]'),
    'ContinuousCohomology.homologyQuotientIso_natural_assoc': (528, '@[reassoc]'),
    'ContinuousGroupCohomology.LevelCompact.RestrictedLevelSystem.mk': (142, '/-- A compatible choice of closed residual subrepresentation at every open'),
    'ContinuousGroupCohomology.LevelCompact.mem_universalNormSubmodule_iff': (48, 'theorem mem_universalNormSubmodule_iff (A : Rep.{u} R G)'),
    'ContinuousGroupCohomology.LevelCompact.mk': (88, '/-- Compact Hausdorff additive-group topologies on the invariants under every'),
    'ContinuousGroupCohomology.LevelCompactRep.Hom.ext_iff': (58, '@[ext]'),
    'ContinuousGroupCohomology.LevelCompactRep.Hom.mk': (55, '/-- A morphism of level-compact representations is a representation morphism'),
    'ContinuousGroupCohomology.LevelCompactRep.forget_map': (99, '@[simps, expose]'),
    'ContinuousGroupCohomology.LevelCompactRep.forget_obj': (99, '@[simps, expose]'),
    'ContinuousGroupCohomology.LevelCompactRep.instCategory': (69, 'instance : Category (LevelCompactRep.{uR, uG, uA} R G) where'),
    'ContinuousGroupCohomology.LevelCompactRep.instFaithfulRepForget': (104, 'instance : (forget (R := R) (G := G)).Faithful where'),
    'ContinuousGroupCohomology.LevelCompactRep.mk': (35, '/-- A representation together with compact Hausdorff additive-group'),
    'ContinuousGroupCohomology.finiteNegativeDeflation_naturality_assoc': (145, '@[reassoc]'),
    'ContinuousGroupCohomology.nestedQuotientInvariantsRepIso_naturality_assoc': (104, '@[reassoc]'),
    'ContinuousGroupExtension.Equiv.instEquivLike': (161, "instance : EquivLike (S.Equiv S') E E' where"),
    'ContinuousGroupExtension.Equiv.instHomeomorphClass': (175, "instance : HomeomorphClass (S.Equiv S') E E' where"),
    'ContinuousGroupExtension.Equiv.instMulEquivClass': (172, "instance : MulEquivClass (S.Equiv S') E E' where"),
    'ContinuousGroupExtension.Equiv.mk': (138, '/-- An equivalence of continuous extensions with fixed kernel and quotient.'),
    'ContinuousGroupExtension.Equiv.rightHom_map': (184, '@[simp]'),
    'ContinuousGroupExtension.isSES': (40, 'isSES : TopologicalGroup.IsSES toGroupExtension.inl toGroupExtension.rightHom'),
    'ContinuousGroupExtension.mk': (30, '/-- A group extension whose inclusion and projection form a short exact'),
    'FiniteCoinvariantsNative.instDiscreteTopologyMultiplicativeZModOfNatNat_examples': (133, 'local instance : DiscreteTopology G₂ := ⟨rfl⟩'),
    'FiniteCoinvariantsNative.instTopologicalSpaceMultiplicativeZModOfNatNat_examples': (132, 'local instance : TopologicalSpace G₂ := ⊥'),
    "FiniteNegativeNativeClient.instFintypeSubtypeQuotientMultiplicativeZModOfNatNatSubgroupBotMemMapMk'Top_examples": (77, 'noncomputable local instance : Fintype'),
    'LevelCompactNormNative.instDiscreteTopologyMultiplicativeZModOfNatNat_examples': (109, 'local instance : DiscreteTopology G₂ := ⟨rfl⟩'),
    'LevelCompactNormNative.instTopologicalSpaceMultiplicativeZModOfNatNat_examples': (108, 'local instance : TopologicalSpace G₂ := ⊥'),
    'PointwiseContinuousMulAction.ext_iff': (54, '@[ext]'),
    'PointwiseContinuousMulAction.instCoeFun': (51, 'instance instCoeFun : CoeFun (PointwiseContinuousMulAction G A) (fun _ => G → A → A) :='),
    'PointwiseContinuousMulAction.instNormalClosedDifferenceSubgroup': (120, 'instance instNormalClosedDifferenceSubgroup (ρ : PointwiseContinuousMulAction G A) :'),
    'PointwiseContinuousMulAction.instNormalDifferenceSubgroup': (116, 'instance instNormalDifferenceSubgroup (ρ : PointwiseContinuousMulAction G A) :'),
    'PointwiseContinuousMulAction.mk': (36, '/-- An action by multiplicative automorphisms whose individual values are'),
    'RestrictedLevelNative.instDiscreteTopologyMultiplicativeZModOfNatNat_examples': (150, 'local instance : DiscreteTopology G₂ := ⟨rfl⟩'),
    'RestrictedLevelNative.instTopologicalSpaceMultiplicativeZModOfNatNat_examples': (149, 'local instance : TopologicalSpace G₂ := ⊥'),
    'TopModuleCat.instAdditiveUliftFunctor': (82, "instance : (uliftFunctor.{v', v} R).Additive where"),
    'TopModuleCat.instEssSurjUliftFunctorSameUniverse': (123, '/-- Same-universe lifting of topological modules is essentially surjective. -/'),
    'TopModuleCat.instFaithfulUliftFunctor': (80, "instance : (uliftFunctor.{v', v} R).Faithful := (fullyFaithfulUliftFunctor R).faithful"),
    'TopModuleCat.instFullUliftFunctor': (78, "instance : (uliftFunctor.{v', v} R).Full := (fullyFaithfulUliftFunctor R).full"),
    'TopModuleCat.instIsEquivalenceUliftFunctorSameUniverse': (128, '/-- Same-universe lifting is an equivalence of the category of topological'),
    'TopModuleCat.instLinearUliftFunctor': (139, "instance : (uliftFunctor.{v', v} R).Linear R where"),
    'TopModuleCat.uliftFunctor_map': (57, '@[simps obj map, pp_with_univ]'),
    'TopModuleCat.uliftFunctor_obj': (57, '@[simps obj map, pp_with_univ]'),
    'TopRep.JointlyContinuous.mk': (34, '/-- The action carried by a topological representation is jointly continuous. -/'),
    'TopRep.continuousCohomologyUliftIsoSameUniverse_naturality_assoc': (47, '@[reassoc]'),
    'TopRep.continuousCohomologyUliftMapSameUniverse_comp_assoc': (114, '@[reassoc]'),
    'TopRep.continuousCohomologyUliftMapSameUniverse_eq_map': (89, "/-- The transported same-universe coefficient map is exactly mathlib's native"),
    'TopRep.homogeneousCochainsUliftIsoSameUniverse_naturality_assoc': (297, '@[reassoc]'),
    'TopRep.instAdditiveUliftFunctor': (105, 'instance instAdditiveUliftFunctor : (uliftFunctor (k := k) (G := G) :'),
    'TopRep.instLinearUliftFunctor': (186, 'instance instLinearUliftFunctor : (uliftFunctor (k := k) (G := G) :'),
    'TopRep.jointlyContinuous_ulift_iff': (161, '/-- Joint continuity of an action is equivalent to joint continuity after'),
    'TopRep.normalizedContinuousCohomologyMap_comp_assoc': (95, '@[reassoc]'),
    'TopRep.uliftFunctor_map': (89, '@[simps obj map, pp_with_univ]'),
    'TopRep.uliftFunctor_obj': (89, '@[simps obj map, pp_with_univ]'),
    'TopologicalModN.instContinuousSMul': (86, '/-- Scalar multiplication by the discrete ring `ZMod n` is jointly'),
    'TopologicalModN.instModule': (81, '/-- The closed mod-`n` quotient is canonically a `ZMod n`-module, for every'),
    'TopologicalModN.instT1Space': (100, '/-- The quotient is T1 even when the input group is not. -/'),
    'TopologicalModN.instT2Space': (105, '/-- The quotient is Hausdorff even when the input group is not. -/'),
    'TopologicalModN.instTopologicalSpaceModN': (278, '/-- Algebraic `ModN` carries the quotient topology induced by `ModN.mkQ`. -/'),
    'TopologicalPowerQuotient.instT1Space': (456, '/-- The closed-power quotient is T1 even when the input group is not. -/'),
    'TopologicalPowerQuotient.instT2Space': (461, '/-- The closed-power quotient is Hausdorff even when the input group is not. -/'),
    'ULift.instContinuousSMulOfContinuousSMul': (42, '/-- A scalar action remains continuous after raising the universe of the'),
    'ULift.instIsTopologicalAddGroupOfIsTopologicalAddGroup': (33, '/-- Raising the universe of a topological additive group preserves its'),
    'instCoeSortCompHausAddCommGrpType': (44, 'instance : CoeSort CompHausAddCommGrp (Type u) where'),
}
CATALOGUE_NAMES = {
    'ContinuousGroupCohomology.ClosedTopologicalCoinvariants': (
        'ContinuousGroupExtension.Equiv.quotientConjActTopologicalAbelianizationCoinvariantsEquiv_mk',
        'PointwiseContinuousMulAction.congr_mk',
        'PointwiseContinuousMulAction.map_comp',
        'PointwiseContinuousMulAction.map_id',
        'PointwiseContinuousMulAction.isEquivariant_id',
        'PointwiseContinuousMulAction.map_mk',
        'PointwiseContinuousMulAction.hom_ext',
        'PointwiseContinuousMulAction.lift_mk',
        'PointwiseContinuousMulAction.liftOfClosed_mk',
        'PointwiseContinuousMulAction.algebraicLift_algebraicMk',
        'PointwiseContinuousMulAction.algebraicToClosed_surjective',
        'PointwiseContinuousMulAction.algebraicToClosed_algebraicMk',
        'PointwiseContinuousMulAction.coinvariantsMk_apply',
        'PointwiseContinuousMulAction.instNormalClosedDifferenceSubgroup',
        'PointwiseContinuousMulAction.instNormalDifferenceSubgroup',
        'PointwiseContinuousMulAction.trivial_apply',
        'PointwiseContinuousMulAction.continuousMulEquiv_apply',
        'PointwiseContinuousMulAction.map_mul',
        'PointwiseContinuousMulAction.map_one',
        'PointwiseContinuousMulAction.ext_iff',
        'PointwiseContinuousMulAction.ext',
        'PointwiseContinuousMulAction.instCoeFun',
        'PointwiseContinuousMulAction.mk',
    ),
    'ContinuousGroupCohomology.CompactAddCommGroup': (
        'CompHausAddCommGrp.quotientRangeMap_mk',
        'CompHausAddCommGrp.kernelMap_apply',
        'CompHausAddCommGrp.quotientRangeπ_comp_apply',
        'CompHausAddCommGrp.quotientRangeπ_apply',
        'CompHausAddCommGrp.comp_kernelι_apply',
        'CompHausAddCommGrp.kernelι_apply',
        'CompHausAddCommGrp.instFaithfulCompHausForget₂ContinuousAddMonoidHomCarrierToTopTrueToCompHausContinuousMap',
        'CompHausAddCommGrp.hom_ext_iff',
        'CompHausAddCommGrp.hom_ext',
        'CompHausAddCommGrp.hom_comp',
        'CompHausAddCommGrp.hom_id',
        'CompHausAddCommGrp.instCoeFunHomForallCarrierToTopTrueToCompHaus',
        'CompHausAddCommGrp.instConcreteCategoryContinuousAddMonoidHomCarrierToTopTrueToCompHaus',
        'CompHausAddCommGrp.instCategory',
        'CompHausAddCommGrp.Hom.ext_iff',
        'CompHausAddCommGrp.Hom.ext',
        'CompHausAddCommGrp.Hom.mk',
        'CompHausAddCommGrp.coe_of',
        'instCoeSortCompHausAddCommGrpType',
        'CompHausAddCommGrp.mk',
    ),
    'ContinuousGroupCohomology.CompactAddCommGroupLimits': (
        'CompHausAddCommGrp.instHasLimitsOfShape',
        'CompHausAddCommGrp.instPreservesLimitCompHausForget₂ContinuousAddMonoidHomCarrierToTopTrueToCompHausContinuousMap',
        'CompHausAddCommGrp.instHasLimit',
        'CompHausAddCommGrp.instIsTopologicalAddGroupCarrierToTopTruePtCompHausLimitConeCompForget₂ContinuousAddMonoidHomToCompHausContinuousMap',
        'CompHausAddCommGrp.instAddCommGroupCarrierToTopTruePtCompHausLimitConeCompForget₂ContinuousAddMonoidHomToCompHausContinuousMap',
    ),
    'ContinuousGroupCohomology.CompactFiniteHomology': (
        'CompHausAddCommGrp.homologyMap_mk',
        'CompHausAddCommGrp.boundaryToKernel_apply',
        'CompHausAddCommGrp.finiteFinsuppMap_apply',
    ),
    'ContinuousGroupCohomology.Composition': (
        'ContinuousCohomology.CorestrictionTransversal.corestrictionOneWithTransversal_trans',
        'ContinuousCohomology.CorestrictionTransversal.transDegreeOne_eq_map',
        'ContinuousCohomology.CorestrictionTransversal.degreeOneIso_trans',
        'ContinuousCohomology.CorestrictionTransversal.homologyQuotientIso_trans_assoc',
        'ContinuousCohomology.CorestrictionTransversal.homologyQuotientIso_trans',
        'ContinuousCohomology.CorestrictionTransversal.cocyclesOneCrossedIso_trans',
        'ContinuousCohomology.CorestrictionTransversal.transferQuotient_trans',
        'ContinuousCohomology.CorestrictionTransversal.crossedTrans_comp_mkQL',
        'ContinuousCohomology.CorestrictionTransversal.crossedQuotientTrans_mk',
        'ContinuousCohomology.CorestrictionTransversal.crossedTrans_principal',
        'ContinuousCohomology.CorestrictionTransversal.transferCrossed_trans',
        'ContinuousCohomology.CorestrictionTransversal.next_transRightTransversal',
        'ContinuousCohomology.CorestrictionTransversal.factor_transRightTransversal',
        'ContinuousCohomology.CorestrictionTransversal.transRightTransversal_equiv',
        'ContinuousCohomology.CorestrictionTransversal.transRightRepEquiv_apply_coe',
        'ContinuousCohomology.CorestrictionTransversal.coe_transRightTransversal',
        'ContinuousCohomology.CorestrictionTransversal.towerRepEquiv_apply_coe',
        'ContinuousCohomology.CorestrictionTransversal.towerRep_injective',
        'ContinuousCohomology.crossedTrans_apply',
        'OpenSubgroup.transFiniteIndex',
        'OpenSubgroup.transEquiv_symm_apply',
        'OpenSubgroup.transEquiv_apply',
        'OpenSubgroup.trans_toSubgroup',
    ),
    'ContinuousGroupCohomology.ContinuousGroupExtension': (
        'ContinuousGroupExtension.Equiv.rightHom_map',
        'ContinuousGroupExtension.Equiv.map_inl',
        'ContinuousGroupExtension.Equiv.instHomeomorphClass',
        'ContinuousGroupExtension.Equiv.instMulEquivClass',
        'ContinuousGroupExtension.Equiv.instEquivLike',
        'ContinuousGroupExtension.Equiv.toContinuousMulEquiv',
        'ContinuousGroupExtension.Equiv.mk',
        'ContinuousGroupExtension.commonUniverseUlift_rightHom_apply',
        'ContinuousGroupExtension.commonUniverseUlift_inl_apply',
        'ContinuousGroupExtension.commonUniverseUlift_toGroupExtension',
        'ContinuousGroupExtension.ulift_rightHomContinuous_apply',
        'ContinuousGroupExtension.ulift_inlContinuous_apply',
        'ContinuousGroupExtension.ulift_rightHom_apply',
        'ContinuousGroupExtension.ulift_inl_apply',
        'ContinuousGroupExtension.ulift_toGroupExtension',
        'ContinuousGroupExtension.rightHomContinuous_apply',
        'ContinuousGroupExtension.inlContinuous_apply',
        "ContinuousGroupExtension.mk'_toGroupExtension",
        'ContinuousGroupExtension.toGroupExtension',
        'ContinuousGroupExtension.mk',
    ),
    'ContinuousGroupCohomology.Corestriction': (
        'ContinuousCohomology.CorestrictionTransversal.transferQuotient_comp_restrict_hom_assoc',
        'ContinuousCohomology.CorestrictionTransversal.transferQuotient_comp_restrict_hom',
        'ContinuousCohomology.CorestrictionTransversal.transferQuotient_comp_restrict',
        'ContinuousCohomology.CorestrictionTransversal.transferCrossed_restrict',
        'ContinuousCohomology.CorestrictionTransversal.transferCrossed_restrict_apply',
        'ContinuousCohomology.CorestrictionTransversal.transfer_restrict_term',
        'ContinuousCohomology.CorestrictionTransversal.homologyQuotientIso_restrict_assoc',
        'ContinuousCohomology.CorestrictionTransversal.homologyQuotientIso_restrict',
        'ContinuousCohomology.CorestrictionTransversal.cocyclesOneCrossedIso_restrict',
        'ContinuousCohomology.CorestrictionTransversal.crossedRestrict_comp_mkQL',
        'ContinuousCohomology.CorestrictionTransversal.crossedQuotientRestrict_mk',
        'ContinuousCohomology.CorestrictionTransversal.crossedRestrict_principal',
        'ContinuousCohomology.CorestrictionTransversal.crossedRestrict_apply',
        'ContinuousCohomology.CorestrictionTransversal.transferQuotient_natural',
        'ContinuousCohomology.CorestrictionTransversal.transfer_mkQL_change',
        'ContinuousCohomology.CorestrictionTransversal.transferCrossed_principal',
        'ContinuousCohomology.CorestrictionTransversal.transferCoefficient_apply',
        'ContinuousCohomology.CorestrictionTransversal.transferCrossed_change',
        'ContinuousCohomology.CorestrictionTransversal.transferCrossed_natural',
        'ContinuousCohomology.CorestrictionTransversal.transferCrossed_apply',
        'ContinuousCohomology.CorestrictionTransversal.transferRaw_crossed',
        'ContinuousCohomology.CorestrictionTransversal.transferRaw_change',
        'ContinuousCohomology.CorestrictionTransversal.transferRaw_apply',
        'ContinuousCohomology.CorestrictionTransversal.transfer_term_change',
        'ContinuousCohomology.CorestrictionTransversal.rho_factor_change',
        'ContinuousCohomology.CorestrictionTransversal.rho_inv_factor',
        'ContinuousCohomology.CorestrictionTransversal.transversalFintype',
        'ContinuousCohomology.CorestrictionTransversal.rho_inv_changeFactor',
        'ContinuousCohomology.CorestrictionTransversal.rho_mul_apply',
        'ContinuousCohomology.CorestrictionTransversal.crossed_inv',
        'ContinuousCohomology.CorestrictionTransversal.crossed_one',
        'ContinuousCohomology.CorestrictionTransversal.factor_change',
        'ContinuousCohomology.CorestrictionTransversal.changeRep_next',
        'ContinuousCohomology.CorestrictionTransversal.changeRep_rightCoset',
        'ContinuousCohomology.CorestrictionTransversal.changeFactor_mul_changeRep',
        'ContinuousCohomology.CorestrictionTransversal.inv_mul_factor',
        'ContinuousCohomology.CorestrictionTransversal.next_mul',
        'ContinuousCohomology.CorestrictionTransversal.factor_mul',
        'ContinuousCohomology.CorestrictionTransversal.equiv_mul',
        'ContinuousCohomology.CorestrictionTransversal.factor_one',
        'ContinuousCohomology.CorestrictionTransversal.next_one',
        'ContinuousCohomology.CorestrictionTransversal.factor_mul_next',
    ),
    'ContinuousGroupCohomology.DegreeOne': (
        'ContinuousCohomology.degreeOneIso_inv',
        'ContinuousCohomology.π_comp_homologyQuotientIso',
        'ContinuousCohomology.boundaryArrowIso',
        'ContinuousCohomology.toCycles_comp_cocyclesOneCrossedIso',
        'ContinuousCohomology.boundaryToOneKer_comm',
        'ContinuousCohomology.toCycles_comp_cocyclesOneIso',
        'ContinuousCohomology.cocyclesOneCrossedIso_hom_apply',
        'ContinuousCohomology.cocyclesOneIso_hom_comp_kerι',
        'ContinuousCohomology.crossedMap_comp_mkQL',
        'ContinuousCohomology.principalToCrossedL_toLinearMap',
        'ContinuousCohomology.oneKerCrossedIso',
        'ContinuousCohomology.cochainsZeroIso',
        'ContinuousCohomology.continuous_homogeneousOne',
        'ContinuousCohomology.oneKer_isCrossed',
        'ContinuousCohomology.homogeneousOne_mem_ker',
        'ContinuousCohomology.homogeneousOne_mem_invariants',
        'ContinuousCohomology.crossedQuotientMap_comp',
        'ContinuousCohomology.crossedQuotientMap_id',
        'ContinuousCohomology.crossedMap_comp',
        'ContinuousCohomology.crossedMap_id',
        'ContinuousCohomology.crossedQuotientMap_mk',
        'ContinuousCohomology.crossedMap_principal',
        'ContinuousCohomology.crossedMap_apply',
    ),
    'ContinuousGroupCohomology.FiniteCoinvariants': (
        'ContinuousGroupCohomology.LevelCompact.normFromFiniteCoinvariants_mk',
        'ContinuousGroupCohomology.LevelCompact.finiteCoinvariantsMk_apply',
        'ContinuousGroupCohomology.finiteCoinvariantsMap_mk',
        'ContinuousGroupCohomology.finiteCoinvariantsDesc_mk',
        'ContinuousGroupCohomology.finiteCoinvariantsMk_apply',
        'ContinuousGroupCohomology.finiteOrbitDifferenceHom_range',
        'ContinuousGroupCohomology.finiteOrbitDifference_single',
        'ContinuousGroupCohomology.finiteOrbitDifference_apply',
    ),
    'ContinuousGroupCohomology.GroupExtensionUlift': (
        'GroupExtension.ulift_rightHom_apply',
        'GroupExtension.ulift_inl_apply',
        'ContinuousMulEquiv.ulift_symm_apply',
        'ContinuousMulEquiv.ulift_apply',
    ),
    'ContinuousGroupCohomology.LevelCompact': (
        'ContinuousGroupCohomology.LevelCompact.inclusion_injective',
        'ContinuousGroupCohomology.LevelCompact.inclusion_self',
        'ContinuousGroupCohomology.LevelCompact.inclusion_coe',
        'ContinuousGroupCohomology.LevelCompact.continuous_transport',
        'ContinuousGroupCohomology.LevelCompact.topologicalAddGroup',
        'ContinuousGroupCohomology.LevelCompact.t2',
        'ContinuousGroupCohomology.LevelCompact.compact',
        'ContinuousGroupCohomology.LevelCompact.topology',
        'ContinuousGroupCohomology.LevelCompact.mk',
        'ContinuousGroupCohomology.openSubgroupInvariantsTransport_coe',
    ),
    'ContinuousGroupCohomology.LevelCompactFunctoriality': (
        'ContinuousGroupCohomology.LevelCompactRep.mapInvariants_coe',
        'ContinuousGroupCohomology.LevelCompactRep.instFaithfulRepForget',
        'ContinuousGroupCohomology.LevelCompactRep.forget_obj',
        'ContinuousGroupCohomology.LevelCompactRep.forget_map',
        'ContinuousGroupCohomology.LevelCompactRep.instCategory',
        'ContinuousGroupCohomology.LevelCompactRep.Hom.ext',
        'ContinuousGroupCohomology.LevelCompactRep.Hom.ext_iff',
        'ContinuousGroupCohomology.LevelCompactRep.Hom.mk',
        'ContinuousGroupCohomology.LevelCompactRep.mk',
    ),
    'ContinuousGroupCohomology.LevelCompactNorm': (
        'ContinuousGroupCohomology.LevelCompact.relativeNormWithTransversal_coe',
        'ContinuousGroupCohomology.LevelCompact.relativeNormTransversalFintype',
        'ContinuousGroupCohomology.LevelCompact.relativeNormSubgroup_finiteIndex',
    ),
    'ContinuousGroupCohomology.LowDegreeExact': (
        'ContinuousCohomology.TopologicallySplitShortExact.connectingMap_apply',
        'ContinuousCohomology.TopologicallySplitShortExact.connectingQuotient_withSection',
        'ContinuousCohomology.TopologicallySplitShortExact.connectingQuotient_withRetract',
        'ContinuousCohomology.TopologicallySplitShortExact.connectingQuotient_apply',
        'ContinuousCohomology.TopologicallySplitShortExact.connectingCrossed_change_section',
        'ContinuousCohomology.TopologicallySplitShortExact.connectingCrossed_withRetract',
        'ContinuousCohomology.TopologicallySplitShortExact.connectingCrossed_apply',
        'ContinuousCohomology.TopologicallySplitShortExact.p_section_defect_eq_zero',
        'ContinuousCohomology.TopologicallySplitShortExact.connectingRawMap_apply',
        'ContinuousCohomology.TopologicallySplitShortExact.sectionOnInvariants_apply',
        'ContinuousCohomology.TopologicallySplitShortExact.invariantsProjection_apply',
        'ContinuousCohomology.TopologicallySplitShortExact.invariantsInclusion_apply',
        'ContinuousCohomology.TopologicallySplitShortExact.Hom.p_comm_apply',
        'ContinuousCohomology.TopologicallySplitShortExact.Hom.i_comm_apply',
        'ContinuousCohomology.TopologicallySplitShortExact.Hom.p_comm',
        'ContinuousCohomology.TopologicallySplitShortExact.Hom.i_comm',
        'ContinuousCohomology.TopologicallySplitShortExact.Hom.mk',
        'ContinuousCohomology.TopologicallySplitShortExact.p_section_apply',
        'ContinuousCohomology.TopologicallySplitShortExact.retract_i_apply',
        'ContinuousCohomology.TopologicallySplitShortExact.p_i',
        'ContinuousCohomology.TopologicallySplitShortExact.mk',
    ),
    'ContinuousGroupCohomology.Mackey': (
        'ContinuousCohomology.CorestrictionTransversal.mackeyAssembledRepresentativeMem_coe',
        'ContinuousCohomology.CorestrictionTransversal.mackeyDoubleCosetSummand_mk',
        'ContinuousCohomology.CorestrictionTransversal.mackeyRepresentative_transferTerm',
        'ContinuousCohomology.CorestrictionTransversal.mackeyRepresentativeTransversal_next',
        'ContinuousCohomology.CorestrictionTransversal.mackeyRepresentativeTransversal_factor',
        'ContinuousCohomology.CorestrictionTransversal.mackeyRepresentativeTransversalEquiv_coe',
        'ContinuousCohomology.CorestrictionTransversal.openSubgroupConjugationHom_apply',
        'ContinuousCohomology.CorestrictionTransversal.mackeySummandQuotientWithTransversal_mk',
        'ContinuousCohomology.CorestrictionTransversal.mackeyConjugateQuotient_mk',
        'ContinuousCohomology.CorestrictionTransversal.mackeyConjugateCrossed_apply',
        'ContinuousCohomology.CorestrictionTransversal.mackeyOpenStabilizer_toSubgroup',
        'ContinuousCohomology.CorestrictionTransversal.conjugateTransversalEquiv_coe',
    ),
    'ContinuousGroupCohomology.NestedInvariants': (
        'ContinuousGroupCohomology.nestedQuotientInvariantsRepNatTrans_app',
        'ContinuousGroupCohomology.nestedQuotientInvariantsRepIso_hom_apply_val',
        'ContinuousGroupCohomology.nestedQuotientInvariantsEquiv_symm_apply_val',
        'ContinuousGroupCohomology.nestedQuotientInvariantsEquiv_apply_val',
    ),
    'ContinuousGroupCohomology.NormalizedCohomology': (
        'TopRep.normalizedContinuousCohomologyMap_comp_assoc',
        'TopRep.normalizedContinuousCohomologyMap_comp',
        'TopRep.normalizedContinuousCohomologyMap_id',
    ),
    'ContinuousGroupCohomology.RestrictedLevelCompact': (
        'ContinuousGroupCohomology.LevelCompact.universalNormRestrictedLevelSystem_subrepresentation',
        'ContinuousGroupCohomology.LevelCompact.fullRestrictedLevelSystem_subrepresentation',
        'ContinuousGroupCohomology.LevelCompact.RestrictedLevelSystem.relativeNorm_coe',
        'ContinuousGroupCohomology.LevelCompact.RestrictedLevelSystem.mk',
        'ContinuousGroupCohomology.LevelCompact.universalNormSubrepresentation_toSubmodule',
        'ContinuousGroupCohomology.LevelCompact.universalNormSubmodule_le_range',
        'ContinuousGroupCohomology.LevelCompact.mem_universalNormSubmodule_iff',
    ),
    'ContinuousGroupCohomology.TopModuleCatUlift': (
        'TopModuleCat.instLinearUliftFunctor',
        'TopModuleCat.uliftFunctorObjEquiv_symm_naturality',
        'TopModuleCat.uliftFunctorObjEquiv_naturality',
        'TopModuleCat.uliftFunctorObjEquiv_symm_apply',
        'TopModuleCat.uliftFunctorObjEquiv_apply',
        'TopModuleCat.instAdditiveUliftFunctor',
        'TopModuleCat.instFaithfulUliftFunctor',
        'TopModuleCat.instFullUliftFunctor',
        'TopModuleCat.uliftFunctor_map',
        'TopModuleCat.uliftFunctor_obj',
    ),
    'ContinuousGroupCohomology.TopRepUlift': (
        'TopRep.instLinearUliftFunctor',
        'TopRep.uliftEquiv_naturality',
        'TopRep.uliftEquiv_symm_apply',
        'TopRep.uliftEquiv_apply',
        'TopRep.instAdditiveUliftFunctor',
        'TopRep.uliftFunctor_obj',
        'TopRep.uliftFunctor_map',
        'TopRep.uliftMap_apply',
        'TopRep.ulift_ρ_apply',
        'TopRep.JointlyContinuous.continuous_action',
        'TopRep.JointlyContinuous.mk',
    ),
    'ContinuousGroupCohomology.TopologicalModN': (
        'TopologicalPowerQuotient.congr_mk',
        'TopologicalPowerQuotient.map_comp',
        'TopologicalPowerQuotient.map_id',
        'TopologicalPowerQuotient.map_mk',
        'TopologicalPowerQuotient.mkQ_apply',
        'TopologicalModN.compactModNEquiv_mk',
        'TopologicalModN.compactToModN_mk',
        'TopologicalModN.algebraicToClosed_mk',
        'TopologicalModN.modNMk_apply',
        'TopologicalModN.closedMultiples_one',
        'TopologicalModN.multiples_one',
        'TopologicalModN.multiples_zero',
        'TopologicalModN.congr_mk',
        'TopologicalModN.map_mk',
        'TopologicalModN.lift_mk',
        'TopologicalModN.liftOfClosed_mk',
        'TopologicalModN.mkQ_apply',
    ),
    'ContinuousGroupCohomology.TopologicalQuotientConjugationAction': (
        'TopologicalAbelianization.fromAbelianization_apply_of',
    ),
    'examples.FiniteCoinvariantsNative': (
        'FiniteCoinvariantsNative.descended_norm_proper_level',
        'FiniteCoinvariantsNative.properNormalLevel_lt_top',
        'FiniteCoinvariantsNative.properNormalLevel',
        'FiniteCoinvariantsNative.instDiscreteTopologyMultiplicativeZModOfNatNat_examples',
        'FiniteCoinvariantsNative.instTopologicalSpaceMultiplicativeZModOfNatNat_examples',
        'FiniteCoinvariantsNative.descended_norm_continuous',
        'FiniteCoinvariantsNative.descended_norm_on_generators',
        'FiniteCoinvariantsNative.full_level_norm_comparison',
        'FiniteCoinvariantsNative.residual_action_continuous',
        'FiniteCoinvariantsNative.intertwining_map_on_generators',
        'FiniteCoinvariantsNative.invariant_descent_continuous',
        'FiniteCoinvariantsNative.invariant_descends_on_generators',
        'FiniteCoinvariantsNative.quotient_projection',
        'FiniteCoinvariantsNative.orbit_range_closed',
        'FiniteCoinvariantsNative.orbit_range',
        'FiniteCoinvariantsNative.orbit_single',
    ),
    'examples.FiniteNegativeNative': (
        'FiniteNegativeNativeClient.concrete_positive_naturality',
        'FiniteNegativeNativeClient.concrete_positive_degree',
        'FiniteNegativeNativeClient.concrete_degree_zero',
        "FiniteNegativeNativeClient.instFintypeSubtypeQuotientMultiplicativeZModOfNatNatSubgroupBotMemMapMk'Top_examples",
        'FiniteNegativeNativeClient.bottom_lt_top',
        'FiniteNegativeNativeClient.coefficient_naturality',
        'FiniteNegativeNativeClient.factorization',
        'FiniteNegativeNativeClient.transport_component',
    ),
    'examples.LevelCompactNormNative': (
        'LevelCompactNormNative.norm_twoElement_proper_level',
        'LevelCompactNormNative.twoElementBottom_lt_top',
        'LevelCompactNormNative.twoElementBottom',
        'LevelCompactNormNative.instDiscreteTopologyMultiplicativeZModOfNatNat_examples',
        'LevelCompactNormNative.instTopologicalSpaceMultiplicativeZModOfNatNat_examples',
        'LevelCompactNormNative.norm_continuous',
        'LevelCompactNormNative.norm_range_residual_stable',
        'LevelCompactNormNative.norm_residual_action',
        'LevelCompactNormNative.norm_same_level',
        'LevelCompactNormNative.norm_tower',
        'LevelCompactNormNative.norm_with_choice_coe',
        'LevelCompactNormNative.norm_two_choices',
        'LevelCompactNormNative.norm_with_choice',
        'LevelCompactNormNative.normClientTransversalFintype',
    ),
    'examples.RestrictedLevelNative': (
        'RestrictedLevelNative.finite_discrete_proper_norm_range',
        'RestrictedLevelNative.proper_level_norm_range',
        'RestrictedLevelNative.finiteDiscreteLevelCompact',
        'RestrictedLevelNative.twoElementBottom_lt_top',
        'RestrictedLevelNative.twoElementTop',
        'RestrictedLevelNative.twoElementBottom',
        'RestrictedLevelNative.instDiscreteTopologyMultiplicativeZModOfNatNat_examples',
        'RestrictedLevelNative.instTopologicalSpaceMultiplicativeZModOfNatNat_examples',
        'RestrictedLevelNative.canonical_le_full',
        'RestrictedLevelNative.canonical_choice',
        'RestrictedLevelNative.full_choice',
        'RestrictedLevelNative.chosen_norm_group_hom',
        'RestrictedLevelNative.chosen_compact_group',
        'RestrictedLevelNative.chosen_additive_group',
        'RestrictedLevelNative.chosen_hausdorff',
        'RestrictedLevelNative.chosen_compact',
        'RestrictedLevelNative.chosen_norm_continuous',
        'RestrictedLevelNative.chosen_norm_same_level',
        'RestrictedLevelNative.chosen_norm_tower',
        'RestrictedLevelNative.chosen_norm_formula',
        'RestrictedLevelNative.chosen_contains_universal',
        'RestrictedLevelNative.universal_norm_preservation',
        'RestrictedLevelNative.universal_stable',
        'RestrictedLevelNative.universal_in_each_norm_range',
        'RestrictedLevelNative.universal_membership',
    ),
}
CATALOGUE_TOPICS = {
    "ContinuousGroupCohomology.ClosedTopologicalCoinvariants":
        "closed versus algebraic action-difference quotients for pointwise-continuous actions",
    "ContinuousGroupCohomology.CompactAddCommGroup":
        "the category of compact Hausdorff additive commutative groups and continuous homomorphisms",
    "ContinuousGroupCohomology.CompactAddCommGroupLimits":
        "limits of compact Hausdorff additive commutative groups, including the stated indexing hypotheses",
    "ContinuousGroupCohomology.CompactFiniteHomology":
        "finite-stage homology maps for compact additive-group constructions",
    "ContinuousGroupCohomology.Composition":
        "composition of degree-one transfer over towers of open finite-index subgroups",
    "ContinuousGroupCohomology.ContinuousGroupExtension":
        "topological group extensions with the strong short-exact-sequence condition",
    "ContinuousGroupCohomology.Corestriction":
        "transfer in continuous degree-one cohomology for open finite-index subgroups",
    "ContinuousGroupCohomology.DegreeOne":
        "crossed degree-one cocycles, principal cocycles and homology quotients",
    "ContinuousGroupCohomology.FiniteCoinvariants":
        "finite acting groups, orbit-difference relations, coinvariants and norms",
    "ContinuousGroupCohomology.GroupExtensionUlift":
        "universe transport of the named topological group-extension maps",
    "ContinuousGroupCohomology.LevelCompact":
        "compact Hausdorff models of open-subgroup invariant levels",
    "ContinuousGroupCohomology.LevelCompactFunctoriality":
        "functoriality of compact level systems and their invariant maps",
    "ContinuousGroupCohomology.LevelCompactNorm":
        "relative norm maps between compact open-subgroup levels",
    "ContinuousGroupCohomology.LowDegreeExact":
        "connecting morphisms and low-degree exactness for topologically split sequences",
    "ContinuousGroupCohomology.Mackey":
        "the double-coset decomposition of continuous degree-one transfer",
    "ContinuousGroupCohomology.NestedInvariants":
        "iterated invariants under a normal subgroup and its quotient",
    "ContinuousGroupCohomology.NormalizedCohomology":
        "normalization of continuous cohomology and its coefficient maps",
    "ContinuousGroupCohomology.RestrictedLevelCompact":
        "closed restricted level systems and finite-stage relative-norm ranges",
    "ContinuousGroupCohomology.TopModuleCatUlift":
        "universe-lift functors for topological module categories",
    "ContinuousGroupCohomology.TopRepUlift":
        "universe-lift functors and jointly continuous topological representations",
    "ContinuousGroupCohomology.TopologicalModN":
        "closed power subgroups and topological reduction modulo n",
    "ContinuousGroupCohomology.TopologicalQuotientConjugationAction":
        "topological quotient-conjugation actions of group extensions",
    "examples.FiniteCoinvariantsNative":
        "checked finite-coinvariant and descended-norm examples",
    "examples.FiniteNegativeNative":
        "checked concrete finite negative-deflation examples",
    "examples.LevelCompactNormNative":
        "checked relative-norm calculations on compact levels",
    "examples.RestrictedLevelNative":
        "checked restricted-level and norm-range calculations",
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


class Header(HTMLParser):
    """Extract all visible native tokens, including CSS-hidden implicit binders."""

    def __init__(self, value):
        super().__init__(convert_charrefs=True)
        self.stack = []
        self.text = []
        self.kinds = []
        self.names = []
        self.feed(value)
        self.close()
        require(not self.stack, "unclosed native header")

    def handle_starttag(self, tag, attrs):
        require(tag in {"div", "span", "a"}, "unexpected/active native header tag")
        attributes = dict(attrs)
        require(len(attrs) == len(attributes) and set(attributes) <= {"class", "href", "id"},
                "active/unknown native header attribute")
        require(tag == "a" or "href" not in attributes, "unexpected native header link")
        require("id" not in attributes or
                (tag == "span" and re.fullmatch(r"[\w.']+", attributes["id"]) is not None),
                "active/unknown native header id")
        require("href" not in attributes or
                re.fullmatch(r"\./[\w./#'-]+", attributes["href"]) is not None,
                "active/external native header link")
        classes = set(attributes.get("class", "").split())
        if tag == "div" and "decl_type" in classes:
            self.text.append(" ")
        self.stack.append((tag, classes))

    def handle_endtag(self, tag):
        require(bool(self.stack) and self.stack[-1][0] == tag, "unbalanced native header")
        self.stack.pop()

    def handle_data(self, value):
        require(bool(self.stack) or not value.strip(), "text outside native header")
        self.text.append(value)
        if any("decl_kind" in classes for _, classes in self.stack):
            self.kinds.append(value)
        if any("decl_name" in classes for _, classes in self.stack):
            self.names.append(value)

    def handle_comment(self, _):
        raise ValueError("unexpected native header comment")

    def handle_decl(self, _):
        raise ValueError("unexpected native header declaration")

    def rendered(self):
        return " ".join("".join(self.text).split())


def source_anchor(raw, line, name, doc, kind):
    lines = raw.decode("utf-8").splitlines()
    require(type(line) is int and 0 < line <= len(lines), "invalid native source line: " + name)
    source_line = lines[line - 1]
    near = "\n".join(lines[max(0, line - 10):min(len(lines), line + 12)])
    if doc:
        source_comments = re.findall(r"/--(.*?)-/", near, re.DOTALL)
        require(any(" ".join(comment.split()) == " ".join(doc.split())
                    for comment in source_comments),
                "native docstring/source mismatch: " + name)
    elif kind != "ctor":
        require(not source_line.lstrip().startswith("/--"), "native docstring missing: " + name)
    if name in GENERATED_ANCHORS:
        expected_line, exact_marker = GENERATED_ANCHORS[name]
        require(line == expected_line and source_line.strip() == exact_marker,
                "generated source anchor mismatch: " + name)
        short = name.rsplit(".", 1)[-1]
        if short.endswith("_assoc") and source_line.strip() == "@[reassoc]":
            require(re.search(r"\b" + re.escape(short.removesuffix("_assoc")) + r"\b", near)
                    is not None, "generated reassoc parent absent: " + name)
        if kind == "ctor":
            require(re.search(r"\b(structure|class)\b", near) is not None,
                    "generated constructor parent absent: " + name)
    else:
        short = name.rsplit(".", 1)[-1]
        require(re.search(r"(?<![\w'])" + re.escape(short) + r"(?![\w'])", near) is not None,
                "native source/name position differs: " + name)


def check_snapshot(revision, sources):
    require(revision == SOURCE, "unexpected/stale analyzed source revision")
    require(set(sources) == set(SOURCE_INPUT_SHA256), "source/pin inventory differs")
    for path, expected in SOURCE_INPUT_SHA256.items():
        require(digest(sources[path]) == expected, "source/pin drift: " + path)


def catalogue_note(module, name, kind):
    require(module in CATALOGUE_NAMES and name in CATALOGUE_NAMES[module] and
            module in CATALOGUE_TOPICS,
            "missing original catalogue explanation: " + module + "/" + name + "/" + kind)
    short = name.rsplit(".", 1)[-1]
    topic = CATALOGUE_TOPICS[module]
    if kind == "ctor":
        return ("Lean-generated constructor for the source structure/class `" +
                name.rsplit(".", 1)[0] + "`; the structure fields and parameters are in " +
                "the displayed signature and source declaration. " + topic.capitalize() + ".")
    if kind == "instance":
        class_name, type_names = EXPECTED_INSTANCES[module][name]
        return ("Provides the native `" + class_name + "` instance in " + topic +
                (" (native type names: " + ", ".join("`" + value + "`" for value in type_names) + ")"
                 if type_names else "") + "; the displayed signature retains all instance parameters.")
    if (short.startswith("inst") and name in GENERATED_ANCHORS and
            "local instance" in GENERATED_ANCHORS[name][1]):
        return ("Generated declaration of a module-local instance for " + topic +
                "; local instance syntax does not by itself promise a global public instance.")
    if short.endswith("_assoc") and name in GENERATED_ANCHORS:
        return ("Lean-generated reassociated statement associated with `" +
                name.removesuffix("_assoc") + "` in " + topic +
                "; the original `@[reassoc]` source anchor is shown below.")
    if short.endswith("_iff"):
        return ("The iff characterization named `" + short + "` in " + topic +
                "; use the full signature for both directions and their assumptions.")
    if short.endswith("_mk") or short.endswith("_apply"):
        return ("The named computation `" + short + "` for " + topic +
                "; the displayed source type specifies its input and result exactly.")
    if short.endswith("_comp") or short.endswith("_id") or short.endswith("_naturality"):
        return ("The named composition, identity or naturality law `" + short +
                "` for " + topic + "; refer to the signature for the actual hypotheses.")
    action = "Defines" if kind == "def" else "Records a theorem about"
    return (action + " `" + short + "` in " + topic +
            "; the displayed signature, not this orientation text, specifies its exact scope.")


def validate(records, raw_records, sources, revision):
    check_snapshot(revision, sources)
    require(type(records) is dict and type(raw_records) is dict and
            set(records) == set(raw_records) == set(MODULES), "native module inventory differs")
    sections = {"production": {}, "clients": {}}
    undocumented = []
    for module in MODULES:
        record = records[module]
        require(json.loads(raw_records[module]) == record, "native record bytes/JSON differ: " + module)
        require(type(record) is dict and set(record) == {"name", "declarations", "instances", "imports"},
                "native module shape differs: " + module)
        require(record["name"] == module, "native module name differs: " + module)
        require(type(record["declarations"]) is list and
                len(record["declarations"]) == COUNTS[module],
                "missing/extra native declaration: " + module)
        require(type(record["instances"]) is list and type(record["imports"]) is list and
                all(type(item) is str for item in record["imports"]) and
                len(set(record["imports"])) == len(record["imports"]),
                "native instances/imports shape differs: " + module)
        instances = {}
        for instance in record["instances"]:
            require(type(instance) is dict and set(instance) == {"name", "className", "typeNames"}
                    and all(type(instance[field]) is str for field in ("name", "className"))
                    and type(instance["typeNames"]) is list and
                    all(type(value) is str for value in instance["typeNames"]),
                    "malformed native instance row: " + module)
            require(instance["name"] not in instances, "duplicate native instance row: " + module)
            instances[instance["name"]] = (instance["className"], tuple(instance["typeNames"]))
        require(instances == EXPECTED_INSTANCES.get(module, {}),
                "missing/extra/wrong native instance table: " + module)
        path = module.replace(".", "/") + ".lean"
        names, kinds, rows = set(), {}, []
        for row in record["declarations"]:
            require(type(row) is dict and set(row) == {"info", "header"} and
                    type(row["info"]) is dict, "native declaration shape differs: " + module)
            info = row["info"]
            require(set(info) == {"name", "kind", "doc", "docLink", "sourceLink", "line"},
                    "native declaration info shape differs: " + module)
            name, kind = info["name"], info["kind"]
            require(type(name) is str and type(kind) is str and kind in KINDS and
                    re.fullmatch(r"[\w.']+", name) is not None, "wrong native name/kind: " + str(name))
            require(name not in names, "duplicate native declaration: " + name)
            names.add(name)
            kinds[kind] = kinds.get(kind, 0) + 1
            require(type(info["doc"]) is str and type(row["header"]) is str,
                    "malformed native doc/header: " + name)
            raw_revision = SOURCE if module == "examples.NativeCore" else RAW_ORIGIN
            require(info["sourceLink"] == "https://example.invalid/commit/" + raw_revision + "/" + path,
                    "native source module/revision/path differs: " + name)
            doc_module = DOC_LINK_OVERRIDES.get((module, name), module)
            require(info["docLink"] == "./" + doc_module.replace(".", "/") + ".html#" + name,
                    "native self link differs: " + name)
            require("```" not in info["doc"] and
                    re.search(r"<\s*[/!?a-zA-Z][^>\n]*>", info["doc"]) is None,
                    "active/unsupported native docstring: " + name)
            current_line = info["line"] + LINE_OFFSETS.get(module, 0)
            source_anchor(sources[path], current_line, name, info["doc"], kind)
            header = Header(row["header"])
            visible_kind = "".join(header.kinds)
            signature = header.rendered()
            expected_kinds = ({"def", "abbrev", "noncomputable def", "noncomputable abbrev"}
                              if kind == "def" else {"constructor"} if kind == "ctor" else {kind})
            require(visible_kind in expected_kinds and "".join(header.names) == name and
                    signature.startswith(visible_kind + " " + name + " ") and
                    "```" not in signature,
                    "native signature identity/format differs: " + name)
            if kind == "instance":
                require(name in instances, "declaration/instance table mismatch: " + name)
            elif name in instances:
                raise ValueError("instance table kind mismatch: " + name)
            note = None
            if not info["doc"]:
                note = catalogue_note(module, name, kind)
                undocumented.append((module, name))
            rows.append(dict(name=name, kind=kind, path=path, line=current_line,
                             native_origin_line=info["line"], native_origin_revision=raw_revision,
                             signature=signature, doc=info["doc"].strip(), note=note))
        require(kinds == KIND_COUNTS[module], "native declaration kinds differ: " + module)
        require(set(instances) == {row["info"]["name"] for row in record["declarations"]
                                   if row["info"]["kind"] == "instance"},
                "missing native instance declaration: " + module)
        require(digest(raw_records[module]) == NATIVE_RECORD_SHA256[module],
                "native raw record differs from pinned tool/input: " + module)
        section = "production" if module in PRODUCTION else "clients"
        sections[section][module] = (rows, instances)
    require(set(undocumented) == {(module, name) for module, names in CATALOGUE_NAMES.items()
                                  for name in names}, "undocumented catalogue inventory differs")
    return sections


def render(records, raw_records, sources, revision):
    sections = validate(records, raw_records, sources, revision)
    production, clients, instance_rows, module_counts = [], [], [], {}
    lines = ["# Native API reference (historical analyzed snapshot)", "",
             "This index covers the earlier 27-leaf/eight-client graph; it does not index",
             "later modules and clients or the current root's import graph. The linked source is",
             "the [published initial native-core release](" + PUBLISHED_SOURCE_REPOSITORY +
             "/tree/" + PUBLISHED_SOURCE + "), whose 39 analyzed source and pin input bytes",
             "match the original private analysis at `" + SOURCE + "` exactly. This",
             "public display revision is not the raw extraction revision. For later APIs,",
             "use the [current library README](../README.md#what-is-available), Lean sources",
             "and [native finite-stage guide](FiniteStageColimit.md).", "",
             "Analyzed with Lean `v4.34.0-rc2`, mathlib `e37d88a26f3791ed5a93daa1f949af1021b8d103`,",
             "independent doc-gen4 `" + TOOL + "`. All 28 production modules (public root and 27 leaves)",
             "and eight checked-use client modules are indexed below. Each complete native displayed",
             "signature retains its implicit, typeclass and universe binders (native pretty-print",
             "abbreviations `⋯`, where present, are linked to their original unelided source).",
             "Source anchors point into that immutable published tree; 35 native records were reused from `" + RAW_ORIGIN + "`",
             "with explicit +4 line remaps in NestedInvariants and TopModuleCatUlift; NativeCore is renewed",
             "on the final source. Generated entries can point to their parent; raw origin is in the manifest.",
             "Missing Lean docstrings have explicitly labeled, independently written catalogue prose.",
             "Module prose, private declarations and proof bodies are outside this declaration/instance",
             "index. This is not a current complete API, proof, coverage, rights or release check.",
             "[Reproduction and scope](README.md).", ""]
    for section, heading, target in (("production", "Production API", production),
                                     ("clients", "Checked-use clients", clients)):
        lines.extend(["## " + heading, ""])
        for module in (PRODUCTION if section == "production" else CLIENTS):
            rows, instances = sections[section][module]
            module_counts[module] = {"declarations": len(rows), "kinds": KIND_COUNTS[module],
                                     "instances": len(instances)}
            lines.extend(["### " + module, "", f"{len(rows)} native named entries; " +
                          f"{len(instances)} native instance-table rows.", ""])
            if not rows:
                lines.extend(["No new named declarations in this module.", ""])
            for row in sorted(rows, key=lambda item: (item["line"], item["name"])):
                target.append({"module": module, "name": row["name"], "kind": row["kind"],
                               "line": row["line"], "native_origin_line": row["native_origin_line"],
                               "native_origin_revision": row["native_origin_revision"]})
                lines.extend(["#### " + row["name"], "", "Kind: `" + row["kind"] + "`.", "",
                              "```lean", row["signature"], "```", ""])
                if row["note"] is None:
                    lines.extend(["**Native source docstring:** " + row["doc"], ""])
                else:
                    lines.extend(["**Original catalogue explanation (not a Lean docstring):** " +
                                  row["note"], ""])
                lines.extend(["[Source](" + PUBLISHED_SOURCE_URL + "/" + row["path"] + "#L" +
                              str(row["line"]) + ") (historical source start line; generated entries may point to their parent).", ""])
            if instances:
                lines.extend(["#### Native instance table", ""])
                for name, (class_name, type_names) in sorted(instances.items()):
                    instance_rows.append(dict(module=module, name=name, className=class_name,
                                              typeNames=list(type_names)))
                    lines.extend(["- `" + name + "`: `" + class_name + "`; type names: " +
                                  (", ".join("`" + value + "`" for value in type_names)
                                   if type_names else "none"), ""])
    markdown = "\n".join(lines).encode("utf-8")
    manifest = dict(format=1, generator="scripts/generate_api.py", docgen_revision=TOOL,
                    docgen_tree=TOOL_TREE, lean_toolchain="leanprover/lean4:v4.34.0-rc2",
                    mathlib_revision="e37d88a26f3791ed5a93daa1f949af1021b8d103",
                    finite_group_tate_revision="19c1d8ce0f11e9ce7af8ce5ae1e2479aa7cd0796",
                    analyzed_source_revision=SOURCE,
                    analyzed_source_tree=SOURCE_TREE,
                    published_source_revision=PUBLISHED_SOURCE,
                    published_source_repository=PUBLISHED_SOURCE_REPOSITORY,
                    production_modules=list(PRODUCTION),
                    checked_use_client_modules=list(CLIENTS), inputs=SOURCE_INPUT_SHA256,
                    raw_origin_revision=RAW_ORIGIN,
                    raw_module_revisions={module: SOURCE if module == "examples.NativeCore" else RAW_ORIGIN
                                          for module in MODULES},
                    verified_source_line_offsets=LINE_OFFSETS,
                    native_record_sha256=NATIVE_RECORD_SHA256, module_counts=module_counts,
                    normalized_record_sha256={module: digest(json.dumps(records[module],
                        ensure_ascii=False, sort_keys=True, separators=(",", ":")).encode("utf-8"))
                        for module in MODULES},
                    production_declarations=production, checked_use_client_declarations=clients,
                    instance_table=instance_rows, undocumented_count=sum(len(v) for v in CATALOGUE_NAMES.values()),
                    api_sha256=digest(markdown), proof_certification=False, release_acceptance=False)
    return markdown, (json.dumps(manifest, indent=2, sort_keys=True) + "\n").encode("utf-8")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--native-data", type=Path, required=True)
    parser.add_argument("--source-revision", required=True)
    parser.add_argument("--docgen-revision", required=True)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    require(args.docgen_revision == TOOL, "unexpected/stale doc-gen4 revision")
    root = Path(__file__).resolve().parent.parent
    sources = {}
    for path in SOURCE_INPUT_SHA256:
        source_path = root / path
        require(source_path.is_file() and not source_path.is_symlink(), "missing/linked source input: " + path)
        sources[path] = source_path.read_bytes()
    check_snapshot(args.source_revision, sources)
    actual_lean = {path.relative_to(root).as_posix() for directory in
                   (root, root / "ContinuousGroupCohomology", root / "examples")
                   for path in directory.glob("*.lean")}
    require(actual_lean == {module.replace(".", "/") + ".lean" for module in MODULES} |
            {"lakefile.lean"}, "missing/extra shipped Lean module")
    require({path.name for path in root.iterdir()} <= {
        ".git", ".lake", ".gitignore", "LICENSE", "README.md", "formalization.yaml",
        "lean-toolchain", "lakefile.lean", "lake-manifest.json", "ContinuousGroupCohomology.lean",
        "ContinuousGroupCohomology", "examples", "docs", "scripts"}, "unexpected shipped root file")
    scripts = root / "scripts"
    require(scripts.is_dir() and not scripts.is_symlink() and
            {path.name for path in scripts.iterdir()} == {"generate_api.py", "test_generate_api.py"},
            "unexpected adapter script")
    require(args.native_data.is_dir() and not args.native_data.is_symlink(),
            "native data directory absent/linked")
    expected_files = {"declaration-data-" + module + ".bmp" for module in MODULES}
    require({path.name for path in args.native_data.iterdir()} == expected_files,
            "missing/extra native record file")
    raw_records, records = {}, {}
    for module in MODULES:
        path = args.native_data / ("declaration-data-" + module + ".bmp")
        require(path.is_file() and not path.is_symlink(), "missing/linked native record: " + module)
        raw_records[module] = path.read_bytes()
        records[module] = json.loads(raw_records[module])
    api, manifest = render(records, raw_records, sources, args.source_revision)
    docs = root / "docs"
    require(docs.is_dir() and not docs.is_symlink() and
            {path.name for path in docs.iterdir()} in (
                {"attribution.md", "README.md"},
                {"attribution.md", "README.md", "API.md", "api-manifest.json"}),
            "unexpected/missing documentation file")
    for name, content in (("API.md", api), ("api-manifest.json", manifest)):
        target = docs / name
        require(not target.is_symlink(), "linked output refused: " + name)
        if target.exists():
            require(target.is_file() and target.read_bytes() == content,
                    "generated file differs/stale manifest: " + name)
        elif args.check:
            raise ValueError("generated file absent: " + name)
    if not args.check:
        (docs / "API.md").write_bytes(api)
        (docs / "api-manifest.json").write_bytes(manifest)
    print(json.dumps(dict(status="matched" if args.check else "generated",
                          production=len(json.loads(manifest)["production_declarations"]),
                          clients=len(json.loads(manifest)["checked_use_client_declarations"]),
                          instances=len(json.loads(manifest)["instance_table"]),
                          api_sha256=digest(api), proof_certification=False,
                          release_acceptance=False)))


if __name__ == "__main__":
    main()
