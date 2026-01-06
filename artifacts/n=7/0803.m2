                                                                                                                                                                                                                                                                2   2   2   2   2   2   2   2   2   2    2    2
HashTable{AOTideal => ideal (y y   - y y   - y  y  , y y  - y y   + y y  , y y  - y y  - y y , y y  - y y  - y y , y y  - y y  - y y , y y y   - y y y   - y y  y   + y y  y  , y y y   - y y y   - y y  y   + y y  y  , y y y  - y y y   - y y y   + y y y  , y , y , y , y , y , y , y , y , y , y  , y  , y  )}
                              9 10    9 12    10 12   5 7    5 10    7 10   2 4    2 8    4 8   1 4    1 7    4 7   1 3    1 6    3 6   6 7 11    6 7 12    6 11 12    7 11 12   3 4 11    3 4 12    3 11 12    4 11 12   5 6 9    5 6 11    5 9 11    6 9 11   1   2   3   4   5   6   7   8   9   10   11   12
                                2    2    2           2   2   2         2   2   2               2         2   2
          AOTinIdeal => ideal (y  , y  , y  , y y  , y , y , y , y y , y , y , y , y y , y y , y , y y , y , y , y y y  , y y y  , y y y , y y y , y y y , y y y  y  , y y y y  , y y y y , y y y y , y y y y y  , y y y y y )
                                12   11   10   9 10   9   8   7   5 7   6   5   4   2 4   1 4   3   1 3   2   1   6 7 11   3 4 11   5 6 9   1 2 7   3 4 6   5 6 10 11   2 3 8 11   1 2 5 8   2 3 6 7   1 2 6 8 11   2 3 5 6 8
          graph => {set {0, 3}, set {1, 3}, set {3, 5}, set {3, 6}, set {0, 4}, set {0, 5}, set {0, 6}, set {1, 6}, set {2, 4}, set {4, 6}, set {2, 5}, set {2, 6}}
                                  2       3       4       5      6
          hSeries => 1 + 12T + 61T  + 167T  + 257T  + 208T  + 68T
          hyperplanes => {a - d, b - d, d - f, d - g, a - e, a - f, a - g, b - g, c - e, e - g, c - f, c - g}
          numVariables => 12
          WLPfull => "The AOT algebra has WLP"
          WLPin => "A does not have WLP at A_4"


R = QQ[y_1..y_12]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-3}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_9*y_10-y_9*y_12-y_10*y_12, y_5*y_7-y_5*y_10+y_7*y_10, y_2*y_4-y_2*y_8-y_4*y_8, y_1*y_4-y_1*y_7-y_4*y_7, y_1*y_3-y_1*y_6-y_3*y_6, y_6*y_7*y_11-y_6*y_7*y_12-y_6*y_11*y_12+y_7*y_11*y_12, y_3*y_4*y_11-y_3*y_4*y_12-y_3*y_11*y_12+y_4*y_11*y_12, y_5*y_6*y_9-y_5*y_6*y_11-y_5*y_9*y_11+y_6*y_9*y_11, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2, y_9^2, y_10^2, y_11^2, y_12^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-3}, {-3}, {-3}, {-4}, {-4}, {-4}, {-4}, {-5}, {-5}},{{y_12^2, y_11^2, y_10^2, y_9*y_10, y_9^2, y_8^2, y_7^2, y_5*y_7, y_6^2, y_5^2, y_4^2, y_2*y_4, y_1*y_4, y_3^2, y_1*y_3, y_2^2, y_1^2, y_6*y_7*y_11, y_3*y_4*y_11, y_5*y_6*y_9, y_1*y_2*y_7, y_3*y_4*y_6, y_5*y_6*y_10*y_11, y_2*y_3*y_8*y_11, y_1*y_2*y_5*y_8, y_2*y_3*y_6*y_7, y_1*y_2*y_6*y_8*y_11, y_2*y_3*y_5*y_6*y_8}})
G = graph {set {0, 3}, set {1, 3}, set {3, 5}, set {3, 6}, set {0, 4}, set {0, 5}, set {0, 6}, set {1, 6}, set {2, 4}, set {4, 6}, set {2, 5}, set {2, 6}}
