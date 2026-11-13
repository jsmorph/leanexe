"""Published cases of the two-dimensional probability of collision with complete inputs, for
tests/conjunction/benchmark.py.  All lengths are in meters, velocities in meters per second, and
covariances in square meters.  Every number is copied as the source prints it, as a decimal string.

CHAN holds the twelve cases of K. F. Chan, Spacecraft Collision Probability, The Aerospace Press,
2008, chapter 5, in the encounter plane: the mean miss vector, the standard deviations along the
covariance's principal axes, which are the plane's axes, the combined radius, and the probability
to four significant figures.  The book is not openly available.  The inputs and values are those of
Table 1 of J. Bernstein, E. Schlafly, M. Schneider, and C. Miller, Evaluating Space Object
Conjunction Probabilities using Characteristic Function Inversion, LLNL-TR-827434, Lawrence
Livermore National Laboratory, October 2021 (https://www.osti.gov/servlets/purl/1823690), whose
column F(q^2) gives the values of the authors' numerical integration.  That table adapts Table 1 of
R. Serra, D. Arzelier, M. Joldes, J.-B. Lasserre, A. Rondepierre, and B. Salvy, Fast and Accurate
Computation of Orbital Collision Probability for Short-Term Encounters, Journal of Guidance,
Control, and Dynamics 39(5), 2016, and the same twelve values appear in its Alfano, Patera, and
Chan columns as reproduced by M. Joldes's slides "A new method to compute the probability of
collision for short-term space encounters".  The stated precision is the printed one: half a unit
in the fourth significant figure.

ALFANO holds cases 1 to 11 of S. Alfano, Satellite Conjunction Monte Carlo Analysis, AAS 09-233,
AAS/AIAA Space Flight Mechanics Meeting, 2009, appendix A: each object's position, velocity, and
the position block of its covariance in the Earth-centered inertial frame at the time of closest
approach, the combined object radius, and the probabilities of the paper's linear methods, Alfano's
series and Patera's line integral, each with 100 divisions.  NASA's CARA Analysis Tools
(https://github.com/nasa/CARA_Analysis_Tools, commit 43f0160f94d76a91805d86521c3e8fa0d09ecd68)
redistribute the paper in References/ and its data in DataFiles/AlfanoInputData/; the spreadsheets
there hold the same numbers to more digits, and the paper's rounding to ten decimal places changes
none of them by more than 5e-11.  The paper states no precision for these values.  CARA's unit
tests Pc2D_Foster_UnitTest.m and PcCircle_UnitTest.m compare its two-dimensional functions with
the Alfano values of cases 1 to 11 at a relative tolerance of 1e-3, the tolerance used here.
Case 12 has equal velocities at the time of closest approach, so it has no encounter plane, and
CARA's PcCircle returns NaN for it.  Cases 9 and 10 have the same data at the time of closest
approach and differ only in the time span of the paper's long-encounter methods.

A disagreement is a published value farther from the reference than its tolerance.  `cause`
records the cause of each known disagreement; benchmark.py fails on a disagreement without one and
on a recorded cause whose disagreement no longer occurs."""

from typing import NamedTuple


class Value(NamedTuple):
    label: str
    value: str
    cause: str | None = None


class Chan(NamedTuple):
    name: str
    m1: str
    m2: str
    sigma1: str
    sigma2: str
    radius: str
    value: Value


class State(NamedTuple):
    position: tuple[str, str, str]
    velocity: tuple[str, str, str]
    # The entries xx, xy, xz, yy, yz, and zz of the position block of the covariance.
    covariance: tuple[str, str, str, str, str, str]


class Alfano(NamedTuple):
    case: int
    radius: str
    values: list[Value]
    primary: State
    secondary: State


def chan(name, m1, m2, sigma1, sigma2, radius, value):
    return Chan(name, m1, m2, sigma1, sigma2, radius, Value('Chan 2008, 4 figures', value))


CHAN = [
    chan('Chan 1', '10', '0', '50', '25', '5', '9.742e-3'),
    chan('Chan 2', '0', '10', '50', '25', '5', '9.181e-3'),
    chan('Chan 3', '10', '0', '75', '25', '5', '6.571e-3'),
    chan('Chan 4', '0', '10', '75', '25', '5', '6.125e-3'),
    chan('Chan 5', '1000', '0', '3000', '1000', '10', '1.577e-5'),
    chan('Chan 6', '0', '1000', '3000', '1000', '10', '1.011e-5'),
    chan('Chan 7', '10000', '0', '3000', '1000', '10', '6.443e-8'),
    chan('Chan 8', '0', '10000', '3000', '1000', '10', '3.219e-27'),
    chan('Chan 9', '10000', '0', '10000', '1000', '10', '3.033e-6'),
    chan('Chan 10', '0', '10000', '10000', '1000', '10', '9.656e-28'),
    chan('Chan 11', '5000', '0', '3000', '1000', '50', '1.039e-4'),
    chan('Chan 12', '0', '5000', '3000', '1000', '50', '1.564e-9'),
]


def alfano(case, radius, alfano100, patera100, *states, patera_cause=None, extra=()):
    p, v, c, p2, v2, c2 = states
    values = [Value('Alfano n=100', alfano100),
              Value('Patera n=100', patera100, patera_cause), *extra]
    return Alfano(case, radius, values, State(p, v, c), State(p2, v2, c2))


ALFANO = [
    alfano(1, '15', '0.146749549', '0.146749497',
           ('153446.76456028', '41874155.869566', '0'),
           ('3066.8747609105', '-11.3736149565', '0'),
           ('6494.0796232671', '-376.13858334524', '0', '22.559465194894', '0', '1.2050395223076'),
           ('153447.2642029', '41874156.369903', '4.9999660258'),
           ('3066.8647607073', '-11.3636148179', '-0.0000013581'),
           ('6494.2249318545', '-376.15611665373', '-0.000044917291988265', '22.560645821883',
            '0.0000025501472714422', '1.2046746471441')),
    alfano(2, '4', '0.006222267', '0.006222266',
           ('153446.17961085', '41874155.871735', '0'),
           ('3066.8747610694', '-11.3735715995', '0'),
           ('6494.0796358449', '-376.13849196421', '0', '22.559454565828', '0', '1.2050395210891'),
           ('153446.67923983', '41874156.372071', '4.999966026'),
           ('3066.8647608662', '-11.3635714597', '-0.0000013581'),
           ('6494.224944434', '-376.15602526787', '-0.000044917281068031', '22.560635191994',
            '0.0000025501460018111', '1.2046746459254')),
    alfano(3, '15', '0.100351176', '0.100351018',
           ('153951.4752631', '41874153.994752', '0'),
           ('3066.8746235984', '-11.4110245828', '0'),
           ('6494.0687699936', '-376.21742938622', '0', '22.568637218841', '0', '1.2050405732107'),
           ('153951.97327397', '41874156.744625', '2.752074327'),
           ('3066.8646233948', '-0.0449985917', '-11.3560272115'),
           ('6539.7159476886', '-354.4827622708', '-24.21583392685', '19.987684161349',
            '1.3128407317001', '1.2674955658292')),
    alfano(4, '15', '0.049323406', '0.049827212',
           ('-28570333.448385', '-29444167.191947', '0'),
           ('-2264.3786988144', '2161.3955655441', '0'),
           ('3149.7395861594', '-3009.1218002121', '0', '2874.8685578726', '0', '0.045936290392913'),
           ('-28570452.261986', '-29444104.463515', '-3.7579884938'),
           ('-2264.3698138968', '2161.4123960717', '0.0002503315'),
           ('3149.8133559411', '-3009.2292261314', '-0.00034854080727125', '2875.0065497795',
            '0.00033298927638278', '0.045966311979646'),
           patera_cause='PATERA_4'),
    alfano(5, '10', '0.044487386', '0.044653357',
           ('6878090.1622937', '-17948.6785967', '-17948.6785967'),
           ('28.0937771808', '5382.8902061517', '5382.8902061517'),
           ('0.06420452636324', '-18.990691938367', '-18.990691938367', '7904.0447002725',
            '7903.9662413044', '7904.0447002725'),
           ('6878089.1619754', '-17946.678929416', '-17947.678286012'),
           ('28.3937813158', '5383.1902163515', '5382.5902081838'),
           ('0.062112348981822', '-18.552069769383', '-18.550001998859', '7905.3548684174',
            '7904.3953083026', '7903.5927814582'),
           patera_cause='The paper marks this value: "Patera recommends n=360" for a radius that '
                        'spans more than a tenth of a standard deviation, and its value with 360 '
                        'divisions agrees.',
           extra=[Value('Patera n=360', '0.044492344')]),
    alfano(6, '10', '0.004335455', '0.004335454',
           ('6877715.634247', '53834.214039436', '53834.214039436'),
           ('-84.2628278054', '5382.5970952289', '5382.5970952289'),
           ('430.02827939777', '-18393.891381385', '-18393.891381385', '790190.51867865',
            '790186.9676547', '790190.51867865'),
           ('6877716.6344015', '53835.214140512', '53836.213772982'),
           ('-84.1628151363', '5382.6970892007', '5382.4970647006'),
           ('429.35284572627', '-18379.895353487', '-18379.212284332', '790234.93895821',
            '790202.01968289', '790176.20377729')),
    alfano(7, '10', '0.000158147', '0.000158146',
           ('-6877469.169824', '-67773.18379991', '-67773.18379991'),
           ('106.0806288716', '-5382.4047050208', '-5382.4047050208'),
           ('47752.931002152', '-1772101.1180686', '-1772101.1180686', '65779308.882914',
            '65778953.792515', '65779308.882914'),
           ('-6877468.6856734', '-67775.155096794', '-67775.63603513'),
           ('106.2166300696', '-5382.5006947728', '-5382.3006891309'),
           ('47842.556250334', '-1773779.529826', '-1773713.6133993', '65780452.931669',
            '65777653.286419', '65775564.028398')),
    alfano(8, '4', '0.036948008', '0.036947992',
           ('14971649.316903', '-20270398.211949', '4076385.1140421'),
           ('1012.256512097', '1460.8114696427', '3527.3938005475'),
           ('153.41029880099', '250.60609601194', '567.38203178725', '411.01058797583',
            '929.49019659682', '2104.6873950138'),
           ('14971649.362587', '-20270399.371468', '4076387.8292675'),
           ('1012.2574006063', '1460.8115969929', '3527.3938402543'),
           ('153.41084903437', '250.60648831196', '567.38320417048', '411.01040332214',
            '929.49023783034', '2104.6885373437')),
    alfano(9, '6', '0.290146291', '0.290174266',
           ('-5532700.6575059', '20132673.95812', '40010548.546273'),
           ('-1450.9451284357', '-311.6085722286', '-671.3019125023'),
           ('67.013620376984', '14.572096438565', '31.362985178843', '3.2132921306927',
            '6.8233552264667', '14.72880348181'),
           ('-5532694.0174556', '20132676.507378', '40010553.862016'),
           ('-1450.9465079251', '-311.6078572248', '-671.3005315149'),
           ('67.014285755464', '14.572190820724', '31.363196175928', '3.2133009783397',
            '6.8233774594117', '14.728854328372')),
    alfano(10, '6', '0.290146291', '0.290174266',
           ('-5532700.6575059', '20132673.95812', '40010548.546273'),
           ('-1450.9451284357', '-311.6085722286', '-671.3019125023'),
           ('67.013620376984', '14.572096438565', '31.362985178843', '3.2132921306927',
            '6.8233552264667', '14.72880348181'),
           ('-5532694.0174556', '20132676.507378', '40010553.862016'),
           ('-1450.9465079251', '-311.6078572248', '-671.3005315149'),
           ('67.014285755464', '14.572190820724', '31.363196175928', '3.2133009783397',
            '6.8233774594117', '14.728854328372')),
    alfano(11, '4', '0.002672026', '0.002672034',
           ('1315785.8155696', '6751109.2628038', '0'),
           ('-7472.0159764697', '1456.2899595947', '0'),
           ('672549.6029462', '-127037.13594612', '0', '24000.066037901', '0', '0.15424708214425'),
           ('1315711.0953284', '6751123.82529', '0'),
           ('-7472.0320939884', '1456.2072604687', '0'),
           ('672552.41491736', '-127029.95787575', '0', '23997.254065287', '0', '0.15424708214409')),
]
