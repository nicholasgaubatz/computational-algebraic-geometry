                                                                                                                                                                                                                                                          2   2   2   2   2   2   2   2   2   2
HashTable{AOTideal => ideal (y y  - y y  - y y , y y y  - y y y   - y y y   + y y y  , y y y  - y y y   - y y y   + y y y  , y y y  - y y y  - y y y  + y y y , y y y  - y y y  - y y y  + y y y , y y y y  - y y y y  + y y y y  - y y y y  - y y y y , y , y , y , y , y , y , y , y , y , y  )}
                              1 3    1 5    3 5   7 8 9    7 8 10    7 9 10    8 9 10   2 3 9    2 3 10    2 9 10    3 9 10   2 3 7    2 3 8    2 7 8    3 7 8   4 5 6    4 5 8    4 6 8    5 6 8   1 2 4 6    1 2 4 7    1 2 6 7    1 4 6 7    2 4 6 7   1   2   3   4   5   6   7   8   9   10
                                2    2   2   2   2   2   2   2         2   2
          AOTinIdeal => ideal (y  , y , y , y , y , y , y , y , y y , y , y , y y y , y y y , y y y , y y y , y y y y , y y y y , y y y y )
                                10   9   8   7   6   5   4   3   1 3   2   1   7 8 9   2 3 9   2 3 7   4 5 6   1 2 5 9   1 2 5 7   1 2 4 6
          graph => {set {0, 3}, set {3, 5}, set {3, 6}, set {0, 4}, set {0, 6}, set {1, 4}, set {1, 5}, set {1, 6}, set {2, 5}, set {2, 6}}
                                  2       3       4       5      6
          hSeries => 1 + 10T + 44T  + 108T  + 154T  + 119T  + 38T
          hyperplanes => {a - d, d - f, d - g, a - e, a - g, b - e, b - f, b - g, c - f, c - g}
          numVariables => 10
          WLPfull => "The AOT algebra has WLP"
          WLPin => "The AOT algebra has WLP"


R = QQ[y_1..y_10]
AOTideal = ideal map(R^1,R^{{-2}, {-3}, {-3}, {-3}, {-3}, {-4}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_1*y_3-y_1*y_5-y_3*y_5, y_7*y_8*y_9-y_7*y_8*y_10-y_7*y_9*y_10+y_8*y_9*y_10, y_2*y_3*y_9-y_2*y_3*y_10-y_2*y_9*y_10+y_3*y_9*y_10, y_2*y_3*y_7-y_2*y_3*y_8-y_2*y_7*y_8+y_3*y_7*y_8, y_4*y_5*y_6-y_4*y_5*y_8-y_4*y_6*y_8+y_5*y_6*y_8, y_1*y_2*y_4*y_6-y_1*y_2*y_4*y_7+y_1*y_2*y_6*y_7-y_1*y_4*y_6*y_7-y_2*y_4*y_6*y_7, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2, y_9^2, y_10^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-3}, {-3}, {-4}, {-4}, {-4}},{{y_10^2, y_9^2, y_8^2, y_7^2, y_6^2, y_5^2, y_4^2, y_3^2, y_1*y_3, y_2^2, y_1^2, y_7*y_8*y_9, y_2*y_3*y_9, y_2*y_3*y_7, y_4*y_5*y_6, y_1*y_2*y_5*y_9, y_1*y_2*y_5*y_7, y_1*y_2*y_4*y_6}})
G = graph {set {0, 3}, set {3, 5}, set {3, 6}, set {0, 4}, set {0, 6}, set {1, 4}, set {1, 5}, set {1, 6}, set {2, 5}, set {2, 6}}
