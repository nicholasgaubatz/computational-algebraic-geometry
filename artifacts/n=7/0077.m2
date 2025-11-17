                                                                      2   2   2   2   2   2
HashTable{AOTideal => ideal (y y  - y y  - y y , y y  - y y  + y y , y , y , y , y , y , y )}
                              4 5    4 6    5 6   2 3    2 5    3 5   1   2   3   4   5   6
                                2   2         2   2         2   2
          AOTinIdeal => ideal (y , y , y y , y , y , y y , y , y )
                                6   5   4 5   4   3   2 3   2   1
          graph => {set {0, 4}, set {0, 5}, set {0, 6}, set {1, 5}, set {5, 6}, set {1, 6}}
                                 2      3     4
          hSeries => 1 + 6T + 13T  + 12T  + 4T
          hyperplanes => {a - e, a - f, a - g, b - f, f - g, b - g}
          numVariables => 6
          WLPfull => "The AOT algebra has WLP"
          WLPin => "A does not have WLP at A_2"


R = QQ[y_1..y_6]
AOTideal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_4*y_5-y_4*y_6-y_5*y_6, y_2*y_3-y_2*y_5+y_3*y_5, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2, y_6^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}, {-2}},{{y_6^2, y_5^2, y_4*y_5, y_4^2, y_3^2, y_2*y_3, y_2^2, y_1^2}})
G = graph {set {0, 4}, set {0, 5}, set {0, 6}, set {1, 5}, set {5, 6}, set {1, 6}}
