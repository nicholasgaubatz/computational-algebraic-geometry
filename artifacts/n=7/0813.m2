                                                                                                                                                                                                                                                                           2   2   2   2   2   2   2   2   2   2    2
HashTable{AOTideal => ideal (y y  - y y   - y y  , y y  - y y  - y y , y y  - y y  - y y , y y y   - y y y   - y y  y   + y y  y  , y y y   - y y y   - y y  y   + y y  y  , y y y  + y y y  - y y y  - y y y , y y y y  - y y y y   + y y y y   - y y y y   - y y y y  , y , y , y , y , y , y , y , y , y , y  , y  )}
                              8 9    8 11    9 11   2 4    2 7    4 7   2 3    2 6    3 6   6 7 10    6 7 11    6 10 11    7 10 11   3 4 10    3 4 11    3 10 11    4 10 11   1 4 5    1 4 9    1 5 9    4 5 9   1 3 5 8    1 3 5 10    1 3 8 10    1 5 8 10    3 5 8 10   1   2   3   4   5   6   7   8   9   10   11
                                2    2    2         2   2   2   2   2         2         2   2
          AOTinIdeal => ideal (y  , y  , y , y y , y , y , y , y , y , y y , y , y y , y , y , y y y  , y y y  , y y y , y y y , y y y y , y y y y , y y y y y  , y y y y y , y y y y y , y y y y y y  )
                                11   10   9   8 9   8   7   6   5   4   2 4   3   2 3   2   1   6 7 10   3 4 10   3 4 6   1 4 5   1 3 5 8   1 2 5 7   1 3 5 9 10   1 2 5 6 8   1 3 5 6 7   1 2 5 6 9 10
          graph => {set {0, 3}, set {1, 3}, set {3, 5}, set {3, 6}, set {0, 4}, set {1, 5}, set {1, 6}, set {2, 4}, set {4, 6}, set {2, 5}, set {2, 6}}
                                  2       3       4       5      6
          hSeries => 1 + 11T + 52T  + 135T  + 202T  + 163T  + 54T
          hyperplanes => {a - d, b - d, d - f, d - g, a - e, b - f, b - g, c - e, e - g, c - f, c - g}
          numVariables => 11
          WLPfull => "The AOT algebra has WLP"
          WLPin => "A does not have WLP at A_4"


R = QQ[y_1..y_11]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-3}, {-3}, {-3}, {-4}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_8*y_9-y_8*y_11-y_9*y_11, y_2*y_4-y_2*y_7-y_4*y_7, y_2*y_3-y_2*y_6-y_3*y_6, y_6*y_7*y_10-y_6*y_7*y_11-y_6*y_10*y_11+y_7*y_10*y_11, y_3*y_4*y_10-y_3*y_4*y_11-y_3*y_10*y_11+y_4*y_10*y_11, y_1*y_4*y_5+y_1*y_4*y_9-y_1*y_5*y_9-y_4*y_5*y_9, y_1*y_3*y_5*y_8-y_1*y_3*y_5*y_10+y_1*y_3*y_8*y_10-y_1*y_5*y_8*y_10-y_3*y_5*y_8*y_10, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2, y_9^2, y_10^2, y_11^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-3}, {-3}, {-4}, {-4}, {-5}, {-5}, {-5}, {-6}},{{y_11^2, y_10^2, y_9^2, y_8*y_9, y_8^2, y_7^2, y_6^2, y_5^2, y_4^2, y_2*y_4, y_3^2, y_2*y_3, y_2^2, y_1^2, y_6*y_7*y_10, y_3*y_4*y_10, y_3*y_4*y_6, y_1*y_4*y_5, y_1*y_3*y_5*y_8, y_1*y_2*y_5*y_7, y_1*y_3*y_5*y_9*y_10, y_1*y_2*y_5*y_6*y_8, y_1*y_3*y_5*y_6*y_7, y_1*y_2*y_5*y_6*y_9*y_10}})
G = graph {set {0, 3}, set {1, 3}, set {3, 5}, set {3, 6}, set {0, 4}, set {1, 5}, set {1, 6}, set {2, 4}, set {4, 6}, set {2, 5}, set {2, 6}}
