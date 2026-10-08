import bootstrap from '@/content/generated/bootstrap.json';
import { ReviewSite } from '@/components/review-site';
export default function Page() {
  return <ReviewSite bootstrap={bootstrap} />;
}
