                                                                                                                                                                                                                                                     2   2   2   2   2   2   2   2   2   2
HashTable{AOTideal => ideal (y y  - y y  + y y , y y  - y y  - y y , y y y  + y y y  - y y y  - y y y , y y y  + y y y  - y y y  - y y y , y y y  - y y y  - y y y  + y y y , y y y  - y y y  - y y y  + y y y , y y y  - y y y  - y y y  + y y y , y , y , y , y , y , y , y , y , y , y  )}
                              5 6    5 9    6 9   1 4    1 6    4 6   3 4 8    3 4 9    3 8 9    4 8 9   2 4 7    2 4 9    2 7 9    4 7 9   2 3 7    2 3 8    2 7 8    3 7 8   1 3 5    1 3 8    1 5 8    3 5 8   1 2 5    1 2 7    1 5 7    2 5 7   1   2   3   4   5   6   7   8   9   10
                                2    2   2   2   2         2   2         2   2   2
          AOTinIdeal => ideal (y  , y , y , y , y , y y , y , y , y y , y , y , y , y y y , y y y , y y y , y y y , y y y , y y y y , y y y y )
                                10   9   8   7   6   5 6   5   4   1 4   3   2   1   3 4 8   2 4 7   2 3 7   1 3 5   1 2 5   1 3 6 8   1 2 6 7
          graph => {set {0, 4}, set {1, 4}, set {2, 4}, set {4, 6}, set {0, 5}, set {0, 6}, set {1, 5}, set {2, 5}, set {5, 6}, set {3, 6}}
                                  2      3       4      5      6
          hSeries => 1 + 10T + 43T  + 99T  + 126T  + 83T  + 22T
          hyperplanes => {a - e, b - e, c - e, e - g, a - f, a - g, b - f, c - f, f - g, d - g}
          numVariables => 10
          WLPfull => "The AOT algebra has WLP"
          WLPin => "The AOT algebra has WLP"


R = QQ[y_1..y_10]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-3}, {-3}, {-3}, {-3}, {-3}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_5*y_6-y_5*y_9+y_6*y_9, y_1*y_4-y_1*y_6-y_4*y_6, y_3*y_4*y_8+y_3*y_4*y_9-y_3*y_8*y_9-y_4*y_8*y_9, y_2*y_4*y_7+y_2*y_4*y_9-y_2*y_7*y_9-y_4*y_7*y_9, y_2*y_3*y_7-y_2*y_3*y_8-y_2*y_7*y_8+y_3*y_7*y_8, y_1*y_3*y_5-y_1*y_3*y_8-y_1*y_5*y_8+y_3*y_5*y_8, y_1*y_2*y_5-y_1*y_2*y_7-y_1*y_5*y_7+y_2*y_5*y_7, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2, y_7^2, y_8^2, y_9^2, y_10^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-3}, {-3}, {-3}, {-3}, {-3}, {-4}, {-4}},{{y_10^2, y_9^2, y_8^2, y_7^2, y_6^2, y_5*y_6, y_5^2, y_4^2, y_1*y_4, y_3^2, y_2^2, y_1^2, y_3*y_4*y_8, y_2*y_4*y_7, y_2*y_3*y_7, y_1*y_3*y_5, y_1*y_2*y_5, y_1*y_3*y_6*y_8, y_1*y_2*y_6*y_7}})
G = graph {set {0, 4}, set {1, 4}, set {2, 4}, set {4, 6}, set {0, 5}, set {0, 6}, set {1, 5}, set {2, 5}, set {5, 6}, set {3, 6}}
