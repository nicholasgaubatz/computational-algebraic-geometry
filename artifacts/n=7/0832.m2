                                                                                                                                                                                                                                                                                                                                                           2   2   2   2   2   2   2   2   2   2    2    2
HashTable{AOTideal => ideal (y y   - y y   - y  y  , y y  - y y   - y y  , y y  - y y  - y y , y y  - y y  - y y , y y y   - y y y   - y y  y   + y y  y  , y y y   - y y y   - y y  y   + y y  y  , y y y  - y y y   - y y y   + y y y  , y y y  - y y y   - y y y   + y y y  , y y y  + y y y   - y y y   - y y y  , y y y  + y y y  - y y y  - y y y , y , y , y , y , y , y , y , y , y , y  , y  , y  )}
                              8 10    8 12    10 12   8 9    8 11    9 11   2 4    2 7    4 7   2 3    2 6    3 6   6 7 11    6 7 12    6 11 12    7 11 12   3 4 11    3 4 12    3 11 12    4 11 12   6 7 9    6 7 10    6 9 10    7 9 10   3 4 9    3 4 10    3 9 10    4 9 10   1 4 5    1 4 10    1 5 10    4 5 10   1 3 5    1 3 9    1 5 9    3 5 9   1   2   3   4   5   6   7   8   9   10   11   12
                                2    2    2           2         2   2   2   2   2         2         2   2
          AOTinIdeal => ideal (y  , y  , y  , y y  , y , y y , y , y , y , y , y , y y , y , y y , y , y , y y  y  , y y y  , y y y  , y y y , y y y , y y y , y y y , y y y , y y y y , y y y y )
                                12   11   10   8 10   9   8 9   8   7   6   5   4   2 4   3   2 3   2   1   9 10 11   6 7 11   3 4 11   6 7 9   3 4 9   3 4 6   1 4 5   1 3 5   1 2 5 7   1 2 5 6
          graph => {set {0, 3}, set {1, 3}, set {3, 5}, set {3, 6}, set {0, 4}, set {1, 5}, set {1, 6}, set {2, 4}, set {4, 5}, set {4, 6}, set {2, 5}, set {2, 6}}
                                  2       3       4       5      6
          hSeries => 1 + 12T + 62T  + 174T  + 276T  + 231T  + 78T
          hyperplanes => {a - d, b - d, d - f, d - g, a - e, b - f, b - g, c - e, e - f, e - g, c - f, c - g}
          numVariables => 12
          WLPfull => "The AOT algebra has WLP"
          WLPin => "A does not have WLP at A_4"


R = QQ[y_1..y_12]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-3}, {-3}, {-3}, {-3}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_8*y_10-y_8*y_12-y_10*y_12, y_8*y_9-y_8*y_11-y_9*y_11, y_2*y_4-y_2*y_7-y_4*y_7, y_2*y_3-y_2*y_6-y_3*y_6, y_6*y_7*y_11-y_6*y_7*y_12-y_6*y_11*y_12+y_7*y_11*y_12, y_3*y_4*y_11-y_3*y_4*y_12-y_3*y_11*y_12+y_4*y_11*y_12, y_6*y_7*y_9-y_6*y_7*y_10-y_6*y_9*y_10+y_7*y_9*y_10, y_3*y_4*y_9-y_3*y_4*y_10-y_3*y_9*y_10+y_4*y_9*y_10, y_1*y_4*y_5+y_1*y_4*y_10-y_1*y_5*y_10-y_4*y_5*y_10, y_1*y_3*y_5+y_1*y_3*y_9-y_1*y_5*y_9-y_3*y_5*y_9, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2, y_9^2, y_10^2, y_11^2, y_12^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-3}, {-3}, {-3}, {-3}, {-3}, {-3}, {-4}, {-4}},{{y_12^2, y_11^2, y_10^2, y_8*y_10, y_9^2, y_8*y_9, y_8^2, y_7^2, y_6^2, y_5^2, y_4^2, y_2*y_4, y_3^2, y_2*y_3, y_2^2, y_1^2, y_9*y_10*y_11, y_6*y_7*y_11, y_3*y_4*y_11, y_6*y_7*y_9, y_3*y_4*y_9, y_3*y_4*y_6, y_1*y_4*y_5, y_1*y_3*y_5, y_1*y_2*y_5*y_7, y_1*y_2*y_5*y_6}})
G = graph {set {0, 3}, set {1, 3}, set {3, 5}, set {3, 6}, set {0, 4}, set {1, 5}, set {1, 6}, set {2, 4}, set {4, 5}, set {4, 6}, set {2, 5}, set {2, 6}}
