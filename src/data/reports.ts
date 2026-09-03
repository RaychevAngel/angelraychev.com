// Standalone designed documents. Each is self-contained HTML in /public/reports/<slug>/.
export type Report = {
  slug: string;
  title: string;
  description: string;
  date: string;
};

export const reports: Report[] = [
  {
    slug: "configuration-consumption",
    title: "Configuration and Consumption",
    description:
      "Can a non-degenerating human state be reached without genetic change? Six research fronts, adjudicated: the aged state splits into a layer that is a configuration and a layer that is a consumption.",
    date: "2026-09-03",
  },
  {
    slug: "accumulation-decade",
    title: "The Accumulation Decade",
    description:
      "The measurables that carry real evidence, ranked; how to raise each one; the week that does it; and where healthy training stress becomes harmful.",
    date: "2026-08-17",
  },
  {
    slug: "capability-stack",
    title: "The Capability Stack",
    description:
      "A seven-layer framework for physical capability. Capacities overlap, labels bundle, order matters, and environment is a stimulus rather than a setting.",
    date: "2026-08-16",
  },
  {
    slug: "longevity-matrix",
    title: "The Longevity Matrix",
    description:
      "A 2015 athleticism matrix audited against the five-pillar longevity model, with every citation adversarially verified and 33 activities re-scored.",
    date: "2026-08-16",
  },
];
